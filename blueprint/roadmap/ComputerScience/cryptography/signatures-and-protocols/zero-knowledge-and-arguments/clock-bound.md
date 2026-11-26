# Clock bound

Fix a verifier and a finite range with a fixed bitstring encoding, so one constant bounds the length of every encoded initial claim. Let $x$ have length $n$, let $k$ be the scheduled number of messages at $n$, and take a private tape of exactly the scheduled coin count at $n$. For any deterministic prover strategy and any $0\leq i\leq k$, let $v_i$ be the verifier's local view after $i$ messages. If $p_s,p_d$ are the polynomial clocks for the send and decision machines, one polynomial $q$ works for all these choices:

$$
(k+1)\bigl(p_s(|v_i|)+p_d(|v_i|)\bigr)\leq q(n).
$$

There are at most $k+1$ routine calls, including the final decision, so this bounds their total machine time. The clocks do not charge for assembling the views themselves. That overhead is separately polynomial: a view contains the input, bounded claim, scheduled tape, one end marker per message and at most $k$ bounded payloads. Tagging and copying these words takes linear time in their total length per view.
