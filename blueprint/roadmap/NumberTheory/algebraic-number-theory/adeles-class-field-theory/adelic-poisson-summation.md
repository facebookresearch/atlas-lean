# Poisson summation formula for adeles

Let $K$ be a number field with adele ring $\mathbb{A}$. For a place $v$ of $K$ let $\psi_v$ be the standard
additive character of $K_v$: $x \mapsto e^{-2\pi i x}$ on $\mathbb{R}$, the character of
$\mathbb{Q}_p$ trivial on $\mathbb{Z}_p$ with $\psi(1/p^n) = e^{2\pi i / p^n}$, and on a finite extension
the composition of the trace with the character of $\mathbb{R}$ or $\mathbb{Q}_p$. Let
$\psi = \prod_v \psi_v$, a character of $\mathbb{A}$ trivial on $K$, and let $dx = \prod_v dx_v$ be the
product of the Haar measures $dx_v$ on $K_v$ that are self-dual with respect to $\psi_v$. A
Schwartz–Bruhat function on $\mathbb{A}$ is a finite linear combination of products $\prod_v f_v$, with
$f_v$ a Schwartz function on $K_v$ for archimedean $v$, locally constant with compact support for finite
$v$, and equal to the characteristic function of the ring of integers $\mathcal{O}_v$ for all but finitely
many $v$. For such $f$ the Fourier transform $\hat f(y) = \int_{\mathbb{A}} f(x)\, \psi(xy)\, dx$ is again a
Schwartz–Bruhat function, the series $\sum_{\kappa \in K} f(x + \kappa)$ converges absolutely and
uniformly on compact subsets of $\mathbb{A}$, and

$$\sum_{\kappa \in K} f(\kappa) = \sum_{\kappa \in K} \hat f(\kappa).$$

For several infinite places these finite sums of products do not exhaust the Schwartz functions of
$K_\infty = \prod_{v \mid \infty} K_v$; the identity is stated for them, as in Poonen's notes.

## Depends on

- [Additive duality of adeles and the volume of A/K](additive-duality-of-adeles.md), for the standard characters, the self-dual measures and the local Schwartz–Bruhat functions with their Fourier transforms

## Proof depends on

- [Additive duality of adeles and the volume of A/K](additive-duality-of-adeles.md), for $\psi|_K = 1$ and the identification of the annihilator of $K$ with $K$, the volume $1$ of $\mathbb{A}/K$, the summability of $f$ over the translates of fractional ideals, uniformly on compact sets (Poonen's Lemma 5.6), which makes the periodization $\sum_{\kappa \in K} f(x + \kappa)$ continuous, and the Fourier inversion criterion on the compact group $\mathbb{A}/K$, applied to the periodization, whose Fourier coefficients are the values $\hat f(\kappa)$ (Poonen §5.5)

## Sources

- B. Poonen, *Tate's thesis*, lecture notes for MIT 18.786 (Spring 2015), PDF of 2025-10-11,
  <https://math.mit.edu/~poonen/786/notes.pdf>: §4.3, the paragraph after Definition 4.5 (the standard
  characters), §4.4 (local Schwartz–Bruhat functions), §5.2 (the standard global character), §5.3 (the Tamagawa measure),
  §5.4 (Schwartz–Bruhat functions on $\mathbb{A}$ and the adelic Fourier transform), Lemma 5.6
  (convergence), Proposition 5.3 ($\psi$ is trivial on $K$) and Theorem 5.7 (Poisson summation formula
  for $K \subset \mathbb{A}$).
