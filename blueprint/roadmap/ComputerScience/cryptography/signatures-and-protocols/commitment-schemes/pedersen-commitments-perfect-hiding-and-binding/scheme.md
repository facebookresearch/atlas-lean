# Pedersen commitment scheme

The Pedersen commitment scheme with public parameters $g$ and $h$ commits to $m \in \mathbb{Z}/q$ by
drawing a uniform opening $r \in \mathbb{Z}/q$ and publishing $g^m h^r$. Verification recomputes
$g^m h^r$ and compares it with the commitment.
