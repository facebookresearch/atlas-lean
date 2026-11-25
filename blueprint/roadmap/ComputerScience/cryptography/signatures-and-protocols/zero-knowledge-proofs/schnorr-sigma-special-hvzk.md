# Perfect special honest-verifier zero knowledge of Schnorr as a Sigma protocol

If $q \ge 1$ and $g^q = 1$, [Schnorr's protocol as a Sigma protocol](schnorr-sigma-protocol.md) is
[perfectly special honest-verifier zero knowledge](special-hvzk.md) with the
[per-challenge Schnorr simulator](schnorr-sigma-sim-at.md): for every challenge $r$, the answer
$r x + k$ is uniform when $k$ is, and the commitment $g^k$ is then $g^s y^{-r}$.
