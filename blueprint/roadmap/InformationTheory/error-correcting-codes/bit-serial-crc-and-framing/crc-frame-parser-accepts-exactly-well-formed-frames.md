# The CRC frame parser accepts exactly the well-formed frames

Run the [fixed-length frame parser](fixed-length-crc-frame-parser-recovers-encoded-payloads.md) for a monic $g$ over
$\mathbb F_2$ of degree $r \ge 1$ and payload length $l$ on a finite token sequence, starting in $\mathsf{Idle}$. Then it outputs
$\mathsf{accept}(w_0 \dots w_{l-1})$ exactly once for each occurrence of a block $\mathsf{Start}$, $\mathsf{Bit}(w_0), \dots,
\mathsf{Bit}(w_{l+r-1})$, $\mathsf{End}$ of consecutive tokens whose body polynomial $\sum_j w_j X^{l+r-1-j}$ is divisible by
$g$, and at no other time. In particular every other kind of segment is rejected or dropped:

- a $\mathsf{Bit}$ or $\mathsf{End}$ outside a frame (a missing $\mathsf{Start}$) outputs $\mathsf{reject}$;
- an $\mathsf{End}$ after fewer than $l + r$ body bits, or a body bit after $l + r$ of them, rejects the frame;
- a $\mathsf{Start}$ inside a frame rejects the unfinished frame and opens a new candidate frame;
- a frame still open at the end of the input produces no payload.

The proof is a case analysis of the transitions: an $\mathsf{accept}$ is emitted only by an $\mathsf{End}$ in state
$\mathsf{In}(l + r, 0, w)$, which is reached only through a $\mathsf{Start}$ followed by exactly $l + r$ bits and no other token.

## Depends on

- [A fixed-length CRC frame parser recovers every encoded payload](fixed-length-crc-frame-parser-recovers-encoded-payloads.md)

## Sources

- A. S. Tanenbaum and D. J. Wetherall, *Computer Networks*, 5th edition, Pearson, 2011, Chapter 3 (framing and cyclic redundancy checks).
- W. W. Peterson and D. T. Brown, "Cyclic codes for error detection", *Proceedings of the IRE* 49(1):228–235, 1961.
