# Doob's $L^p$ maximal inequality

For a submartingale $(X_n)$ and $1 < p < \infty$, the running maximum $\bar X_n = \max_{0 \le m \le n} X_m^+$
satisfies $E(\bar X_n^{\,p}) \le \big(\frac{p}{p-1}\big)^p E\big((X_n^+)^p\big)$; for a martingale $(Y_n)$ the same bound holds
for $\max_{0 \le m \le n} |Y_m|$ in terms of $E|Y_n|^p$.

## Idea

The maximum of a submartingale up to time $n$ is controlled in $L^p$ by its value at time $n$ alone. For
$p = 2$ and a martingale the constant is $4$: $E \max_{m \le n} Y_m^2 \le 4 E Y_n^2$, which is
[Doob's L² maximal inequality](../doob-s-maximal-inequalities/doob-sq-maximal-ineq.md). The constant grows without bound
as $p \downarrow 1$. The inequality is the key estimate behind the convergence of martingales bounded in $L^p$ for
$p > 1$.

## Statements

- [Doob's $L^p$ maximal inequality](doob-lp-maximal-inequality.md)
- [Doob's maximal inequality for nonnegative submartingales](maximal-ineq.md): the maximal inequality the proof starts from

## Background

- [Martingales, submartingales and supermartingales](../martingales-submartingales-and-supermartingales/README.md): submartingales
