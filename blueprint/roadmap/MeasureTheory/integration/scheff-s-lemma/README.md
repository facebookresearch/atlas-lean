# Scheffé's lemma

Let $\mu$ be a measure, $f_n$ real functions that are $\mu$-almost everywhere strongly measurable
and $g \in L^1(\mu)$. If $f_n \to g$ almost everywhere and $\int |f_n| \, d\mu \to \int |g| \, d\mu$
(in $[0, \infty]$), then $\int |f_n - g| \, d\mu \to 0$: the sequence converges to $g$ in
$L^1(\mu)$.

## Idea

Pointwise convergence alone does not give convergence in $L^1$, because mass can escape: the
functions $n \mathbf{1}_{(0, 1/n)}$ tend to $0$ but all have integral $1$. Scheffé's lemma says that
if no mass is lost, that is if the $L^1$ norms converge, the convergence is in $L^1$. Fatou's lemma
applied to the nonnegative functions $|f_n| + |g| - |f_n - g|$, which tend to $2|g|$, gives
$\limsup \int |f_n - g| \le 0$. In probability it says that probability densities converging
pointwise to a probability density converge to it in total variation. The other statements replace almost-everywhere convergence by
convergence in measure and relate the result to uniform integrability.

## Statements

- [Scheffé's lemma](scheffe-lemma.md)
- [Scheffé's lemma for convergence in measure](tendsto-e-lp-norm-one-of-tendsto-in-meas.md): a variant with convergence in measure.
- [Scheffé's lemma on the real line](tendsto-integral-abs-sub-of-ae-tendsto-o.md): a special case for Lebesgue measure.
- [Convergence in measure with converging L¹ norms implies uniform integrability](uniform-integrable-of-tendsto-in-measure.md): a consequence of the convergence-in-measure form.
- [Uniform integrability equivalences](uniform-integrable-tfae-of-tendsto-in-me.md): the convergence-in-measure form inside an equivalence: for a finite measure, with $f_n$ and $g$ in $L^1(\mu)$ for every $n$ and $f_n \to g$ in measure, $(f_n)$ is uniformly integrable if and only if $f_n \to g$ in $L^1$, if and only if $\|f_n\|_1 \to \|g\|_1$; the first equivalence is the Vitali convergence theorem, and the last condition gives the second by Scheffé's lemma for convergence in measure.
