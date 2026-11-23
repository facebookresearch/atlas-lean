# Integrals against normalized weights do not depend on the weight

Let $G$ be a locally compact, second-countable topological group with its Borel $\sigma$-algebra and
a Haar measure $\mu$, and $T \le G$ a closed subgroup with its Borel $\sigma$-algebra and an
inversion-invariant Haar measure $\tau$. Let $F : G \to \mathbb{C}$ be bounded, measurable and
$T$-invariant, and let $w_1, w_2 : G \to \mathbb{R}$ be nonnegative, measurable and compactly
supported with $\int_T w_i(tx)\, d\tau(t) = 1$ whenever $F(x) \ne 0$. Then
$\int_G F\, w_1\, d\mu = \int_G F\, w_2\, d\mu$.

## Idea

This is how integrals over $T \backslash G$ are defined and compared: the integral of a $T$-invariant
function against any weight normalized on the orbits where the function does not vanish is the
same. The proof unfolds one weight against the other: since $\int_T w_2(tx)\, d\tau(t) = 1$ where
$F(x) \ne 0$, $\int_G F w_1\, d\mu = \int_T \int_G F(x)\, w_1(x)\, w_2(tx)\, d\mu(x)\, d\tau(t)$, and
the substitution $x \mapsto t^{-1} x$, the invariance of $F$ and of $\mu$ and the inversion invariance
of $\tau$ turn this into $\int_G F w_2\, d\mu$. Normalization is needed on every orbit where
$F \ne 0$: for $G = \mathbb{Z}/2$, $T$ trivial, counting measures and $F \equiv 1$, the weights
$\mathbf{1}_{\{e\}}$ and $1$ are both normalized at $e$, but only the second everywhere, and they give
the integrals $1$ and $2$.

## Statements

- [Cutoff independence of integrals of bounded invariant functions](integral-mul-eq-integral-mul-of-integral.md)
- [Bounded invariant functions are integrable against normalized cutoffs](integrable-mul-of-integral-subgroup-tran.md): the weighted functions are integrable, so both integrals are genuine.
- [Subgroup-normalized weights give equal integrals](integral-mul-eq-of-normalized-subgroup.md): a more general form, for any measurable subgroup, with neither boundedness nor compact support; used in the proof.
- [Orbit-normalized cutoffs give equal complex integrals](integral-mul-eq-of-normalized-smul.md): the general form for a group action, complex functions; used in the proof.
- [Orbit-normalized weights give equal nonnegative integrals](lintegral-mul-eq-of-normalized-smul.md): the general form for nonnegative functions, in $[0, \infty]$; used in the proof.
- [Integrability is independent of the orbit-normalized weight](integrable-mul-iff-of-normalized-smul.md): integrability does not depend on the weight either; used in the proof.
- [Positive common integral of cocompact subgroup cutoffs](exists-pos-integral-cutoff-of-cocompact.md): a consequence for a cocompact subgroup: a continuous weight normalized on all of $G$ exists, and all such weights have the same positive integral.

## Background

- [Existence of Bruhat functions](../existence-of-bruhat-functions/README.md): the continuous weight of the cocompact case.
