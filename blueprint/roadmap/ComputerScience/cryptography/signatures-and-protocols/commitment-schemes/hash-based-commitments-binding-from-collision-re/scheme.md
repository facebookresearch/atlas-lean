# Hash-based commitment scheme

With a finite nonempty set of nonces, the hash-based commitment scheme with key $s$ (Katz and Lindell,
Section 5.6.5) commits to $m$ by drawing a uniform nonce $r$ and publishing $H_s(r, m)$, with opening
$r$. Verification recomputes $H_s(r, m)$ and compares it with the commitment.
