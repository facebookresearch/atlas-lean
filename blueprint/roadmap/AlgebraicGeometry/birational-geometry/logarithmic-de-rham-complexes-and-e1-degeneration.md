# Logarithmic de Rham complexes and E₁-degeneration

This node is still to be broken down. It covers the Hodge-theoretic input of Esnault and Viehweg's
algebraic proofs of the [Kodaira](kodaira-vanishing-theorem.md) and
[Kawamata–Viehweg](kawamata-viehweg-vanishing-theorem.md) vanishing theorems: the degeneration at
$E_1$ of the logarithmic de Rham complexes attached to cyclic covers, the vanishing theorems for
restriction maps deduced from it, and the behaviour of the sheaves involved under blowing up. It
follows Esnault and Viehweg's *Lectures on Vanishing Theorems*, Lectures 2–5, 8 and 10.

Its central statement is Theorem 5.1 a): let $X$ be a projective manifold over an algebraically
closed field of characteristic zero, $L$ an invertible sheaf, $N \ge 1$ an integer and $D = \sum_j
\alpha_j D_j$ a normal crossing divisor with $0 < \alpha_j < N$ and $L^N = \mathcal{O}_X(D)$. Then
for every effective divisor $D' = \sum_j \mu_j D_j$ and every $b$ the map $H^b(X, L^{-1}(-D')) \to
H^b(X, L^{-1})$ is surjective, equivalently $H^b(X, \omega_X \otimes L) \to H^b(X, \omega_X(D')
\otimes L)$ is injective.

A good expansion has pages for:

- logarithmic differential forms $\Omega^a_X(\log D)$ along a reduced normal crossing divisor, their
  local frames and residue sequences (Definition 2.1, Properties 2.2–2.3), integrable logarithmic
  connections and their residues (2.4–2.8), and the quasi-isomorphisms between logarithmic de Rham
  complexes given by residue conditions (Properties 2.9 and Lemma 2.10);
- the sheaves $L^{(i)} = L^i(-\lfloor \frac{i}{N} D \rfloor)$ for $0 \le i < N$ (Notation 3.1 (c))
  and the divisors $D^{(i)} = \sum_{N \nmid i\alpha_j} D_j$ (Theorem 3.2), and the **normalized**
  cyclic cover $\pi \colon Y \to X$ obtained by taking the $N$-th root of a section of $L^N$ with
  divisor $D = \sum_j \alpha_j D_j$, the normalization of the cyclic algebra $\bigoplus_i L^{-i}$,
  or the disjoint union of the normalizations of its components (3.5): it is the normalization whose
  direct image is $\bigoplus_{i=0}^{N-1} L^{(i)\,-1}$ (3.7, Claim 3.10 and Corollary 3.11), the raw
  algebra not being normal in general (for $N = 3$ and a local branch $t^2$, $k[t, u]/(u^3 - t^2)$
  is not normal, and the floor for $i = 2$ is $1$); with the logarithmic connections on the
  $L^{(i)\,-1}$ (Lemma 3.16); and Theorem 3.2: the residues of these connections (a), equal to
  $\{i\alpha_j/N\}$ along $D_j$, the $E_1$-degeneration of the spectral sequence of the logarithmic
  de Rham complex $\Omega^\bullet_X(\log D^{(i)}) \otimes L^{(i)\,-1}$ (b), and its variant (c) with
  reduced divisors $A$ and $B$ without common components with one another or with $D^{(i)}$, the
  total divisor having normal crossings, and the twist by $-B$;
- Kawamata's covering lemmas (Lemmas 3.17 and 3.19), by which Theorem 3.2 b) in characteristic zero
  follows from the degeneration of the Hodge to de Rham spectral sequence of a projective manifold
  (Remark 3.18), and the fact that cyclic covers have at most quotient singularities (Lemma 3.24);
- the degeneration at $E_1$ of the Hodge to de Rham spectral sequence of a proper smooth variety
  over a field of characteristic zero (Theorem 8.2), obtained algebraically from the theorem of
  Deligne and Illusie (Theorem 8.3: a proper smooth variety over a perfect field of characteristic
  $p \ge \dim X$ lifting to $W_2(k)$) by reduction to characteristic $p$ (Proposition 8.4), or, for
  **projective** varieties, from classical Hodge theory, GAGA and flat base change (8.1), which
  alone do not cover proper nonprojective varieties; and its logarithmic form in characteristic zero
  for a reduced normal crossing divisor $D = A + B$ (Corollary 10.23), which completes the proof of
  Theorem 3.2 c), the characteristic $p$ argument then requiring a lifting of the **pair** $(X, D)$
  to $W_2(k)$, not of $X$ alone (3.2, 8.11, 10.17–10.21);
- the vanishing for restriction maps (Lemma 4.2, with Variant 4.3 and Lemma 4.4), from which Theorem
  5.1 follows through Theorem 3.2 c);
- Claim 5.13: for $X$, $L$, $N$ and a normal crossing divisor $D$ as in Corollary 5.12, a proper
  birational morphism $\tau \colon X' \to X$ such that $\tau^* D$ has normal crossings and $M =
  \tau^* L$, one has $\tau_* M^{(i)\,-1} = L^{(i)\,-1}$ and $R^b \tau_* M^{(i)\,-1} = 0$ for $b >
  0$; the sheaves $M^{(i)}$ are the floor-corrected eigensheaves on $X'$, not the pull-backs of the
  $L^{(i)}$ (for $i = 1$ the added floor can be nonzero, as when one blows up a crossing of two
  components of coefficient $1$ with $N = 2$). Its proof uses that the cyclic covers of $X$ and $X'$
  have quotient singularities and that quotient singularities in characteristic zero are rational,
  which is shown after the claim through the Leray spectral sequence, the splitting of a finite
  direct image by the trace, and the vanishing $R^q g_* \mathcal{O} = 0$, $q > 0$, for a proper
  birational morphism $g$ between nonsingular varieties (pp. 50–51); this last vanishing is a
  separate input, not a consequence of the existence of desingularizations.

The arguments also use Serre's vanishing theorem (Theorem 1.1), Serre duality and GAGA, among the
[standard results of coherent cohomology](standard-results-of-coherent-cohomology.md). Kawamata's
Lemma 5.11 serves only for Corollary 5.12 b) and is not needed for the Kodaira and Kawamata–Viehweg
theorems.

## Depends on

- [Simple normal crossing divisor](simple-normal-crossing-divisor.md), for normal crossing divisors and
  their components

## Proof depends on

- [Standard results of coherent cohomology on projective varieties](standard-results-of-coherent-cohomology.md),
  for Serre vanishing, Serre duality and GAGA
- [Resolution of singularities of quasi-projective varieties](resolution-of-singularities/resolution-of-singularities-of-quasi-projective-varieties.md),
  for the desingularizations of cyclic covers in the proof of Claim 5.13
- [Principalization of ideal sheaves in characteristic zero](resolution-of-singularities/principalization-of-ideal-sheaves.md), to
  make the pull-back of the branch divisor a normal crossing divisor on such a desingularization, in the
  same proof

## Sources

- H. Esnault and E. Viehweg, *Lectures on Vanishing Theorems*, DMV Seminar 20, Birkhäuser, 1992;
  electronic version on H. Esnault's page, <https://page.mi.fu-berlin.de/esnault/books/esvibuch.pdf>
  (page numbers of the electronic version): Lecture 2, 2.1–2.10, pp. 11–17; Notation 3.1 and Theorem
  3.2, pp. 19–20; 3.5–3.16, pp. 22–29; Lemma 3.17, Remark 3.18 and Lemma 3.19, pp. 30–32; Lemma
  3.24, pp. 34–35; Lemma 4.2, Variant 4.3 and Lemma 4.4, pp. 36–37; Theorem 5.1, pp. 42–43; Lemma
  5.11, p. 48; Claim 5.13 and its proof, pp. 49–51; 8.1–8.4, pp. 82–84; 8.11 and 10.17–10.21
  (liftings of pairs); Corollary 10.23, p. 124; Theorem 1.1, p. 4.
