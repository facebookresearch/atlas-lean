/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEADLOCK EXPOSURE IN PACKET SWITCHING NETWORKS is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 5(4)
(1984), 595-609, doi:10.1016/0196-6774(84)90010-5, problem DEADLOCK EXPOSURE IN PACKET
SWITCHING NETWORKS;
S. Toueg and K. Steiglitz, "Some complexity results in the design of deadlock-free packet
switching networks", SIAM Journal on Computing 10(4) (1981), 702-712, doi:10.1137/0210053.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DeadlockExposurePacketSwitchingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DeadlockExposurePacketSwitching

/-!
# DEADLOCK EXPOSURE IN PACKET SWITCHING NETWORKS is NP-complete

INSTANCE (Johnson's column, Dec. 1984): a graph `G = (V, E)`, a positive integer number `b(v)` of
buffers for each vertex `v ∈ V`, a set `R` of packet routes, each `r ∈ R` being a simple path in
`G` from a source vertex `s(r)` to a destination vertex `d(r)`, and for each ordered pair
`(u, v)` of vertices that are the source and destination of some packet route `r ∈ R`, a window
size `w(u, v)`.

QUESTION: is there a possible "deadlock state" for `G` under the "individual end-to-end window"
flow control discipline? A new packet can be started out along `r` only if the network already
contains fewer than `w(s(r), d(r))` packets with source `s(r)` and destination `d(r)`. A deadlock
state consists of a collection `P` of packets, each packet `p` with an assigned route
`r(p) ∈ R` and a current location in a buffer at one of the vertices of `r(p)`; no buffer
contains more than one packet, all the window size bounds are obeyed, and no legal move is
possible. A legal move is one of: (i) if there is a route `r` such that fewer than
`w(s(r), d(r))` packets are currently in transit from `s(r)` to `d(r)`, and `s(r)` has an empty
buffer, a new packet can be generated and assigned route `r` and an empty buffer at `s(r)`;
(ii) a packet that has reached the buffer of its destination vertex `d(r(p))` can be consumed;
(iii) a packet that has not yet reached its destination can be transferred from its current
buffer to a buffer of the next vertex `v` along `r(p)`, provided `v` has an empty buffer.

Representation: vertices are `0, …, n - 1`, edges an undirected simple edge list (`u` and `v`
are adjacent when `(u, v)` or `(v, u)` is listed), `b` a list of `n` positive numbers, the
routes a list without repetitions (`R` is a set), a route a list of vertices (a simple path:
nonempty, no repeated vertex, consecutive vertices adjacent) from its first vertex `s(r)` to its
last vertex `d(r)`, and the windows a list of triples `(u, v, w(u, v))` with one entry for each
source-destination pair of a route and no other entries. A packet is a pair `(ρ, k)`: it follows
route `ρ` and sits at position `k` of that route, i.e. at vertex `r_ρ[k]`. Since buffers at a
vertex are interchangeable, "no buffer contains more than one packet" is "at most `b(v)` packets
at `v`", and "`v` has an empty buffer" is "fewer than `b(v)` packets at `v`". "Packets in
transit from `u` to `v`" counts all packets whose route has source `u` and destination `v`.
Numbers use the canonical binary encoding; the column notes the problem remains NP-complete when
all window sizes and all buffer counts are equal.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DEADLOCK EXPOSURE IN PACKET SWITCHING NETWORKS is NP-complete.** Source: Johnson (1984),
NP-completeness column; Toueg and Steiglitz (1981). -/
public theorem_wanted deadlockExposurePacketSwitching_npComplete :
    deadlockExposurePacketSwitchingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L deadlockExposurePacketSwitchingDec

end MetaMathlibExt.Complexity.NPComplete.DeadlockExposurePacketSwitching
