# Rounding error of the shifted softmax

Fix $n \ge 1$ and $x \in \mathbb{R}^n$. Let $x_{\max} = \max_i x_i$, attained at an index $k$, so $a = x_k = x_{\max}$; let $x_{\min} = \min_i x_i$ and $g = \operatorname{softmax}(x)$. Consider the following evaluation in floating-point arithmetic with unit roundoff $u$: compute $w_i = \exp(x_i - a)$ for every $i$, then $s = \sum_{i \ne k} w_i$ by adding the $w_i$ one at a time, then $\hat g_i = w_i / (1 + s)$. The arithmetic model is that every subtraction, addition and division, and every evaluation of $\exp$ at its computed argument, returns its exact result multiplied by $1 + \delta$ for some $\delta$ with $|\delta| \le u$, where different operations may have different $\delta$.

Then there are constants $C \ge 0$ and $u_0 > 0$, depending only on $n$ and $x$, such that for every $u \in (0, u_0]$ and every evaluation satisfying the model, the computed $\hat g$ satisfies

$$\frac{\|g - \hat g\|_\infty}{\|g\|_\infty} \le \bigl(n + 2 + 2(x_{\max} - x_{\min})\bigr)u + C u^2 .$$

That is, the bound holds up to a remainder that is $O(u^2)$ as $u \to 0$ with $n$ and $x$ fixed, uniformly over all rounding errors allowed by the model. An exponential that underflows violates the model, so such evaluations are outside the statement. The statement gives no explicit value of $C$, and it concerns this two-pass evaluation, not the one-pass online recurrence.

## Depends on

- [Softmax](../../../not-yet-classified/basic/part-06/softmax.md)

## Proof depends on

- [Softmax](../../../not-yet-classified/basic/part-06/softmax.md)

The proof is a direct perturbation analysis of the displayed evaluation under its per-operation error model.

## Sources

- P. Blanchard, D. J. Higham and N. J. Higham, "Accurately computing the log-sum-exp and softmax functions", *IMA Journal of Numerical Analysis* 41(4), 2021; MIMS EPrint 2019.16, Algorithm 4.1 (lines 1–10) and Theorem 4.3, under the per-operation relative-error model of its Section 2, which includes $\exp$ (equations (2.3) and (3.1)).
