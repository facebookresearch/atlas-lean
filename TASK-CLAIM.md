# Task claim: half-period sine sums for odd modulus and for even multiplier

This temporary note opens the draft pull request that claims the ATLAS tasks
`af_8c2efacba4162ee460eedc1e` and `af_94682a5d70e5912a4832a48c`. It will be removed when the
proofs land on this branch.

- Articles: `blueprint/roadmap/Analysis/real-functions/integration/areas-between-cosine-powers/sum-sin-two-pi-mul-div-of-odd.md`
  and `blueprint/roadmap/Analysis/real-functions/integration/areas-between-cosine-powers/sum-sin-pi-mul-div-of-even-of-even.md`
- Lean declarations: `MetaMathlibExt.sum_sin_two_pi_mul_div_of_odd` and
  `MetaMathlibExt.sum_sin_pi_mul_div_of_even_of_even`, two `theorem_wanted` in
  `WantedExt/Analysis/AreasBetweenCosinesWanted.lean`
- Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*, Journal of
  Integer Sequences 28 (2025), Article 25.2.3, Lemmas 6 and 7.

Statements to prove, with their names and statements unchanged:

- for odd $N$ and every natural $q$, $\sum_{\ell=1}^{(N-1)/2} \sin(2\pi q \ell / N)$ equals
  $-\frac{1}{2} \tan\frac{q\pi}{2N}$ if $q$ is even and $\frac{1}{2} \cot\frac{q\pi}{2N}$ if $q$ is odd;
- for positive even $N$ and even $q$, $\sum_{\ell=1}^{N/2} \sin(q \ell \pi / N)$ equals $0$ if
  $q \equiv 0 \pmod 4$ and $\cot(q\pi / (2N))$ if $q \equiv 2 \pmod 4$.
