# Freedman's maximal inequality for adaptive supermartingales

Let $(K_t)_{t<n}$ be a step kernel with adaptive process $P_n$ on a set $\alpha$, and let $(X_k)_{k \le n}$ be a supermartingale along it. Let $b \ge 0$ and let $V_k : \alpha^k \to \mathbb{R}$, $k < n$. Assume that for every $k < n$ and every supported history $h$, the increments $D(x) = X_{k+1}(h, x) - X_k(h)$ satisfy $D(x) \le b$ for every $x$ in the support of $K_k(h)$ and $\sum_x K_k(h)(x) D(x)^2 \le V_k(h)$ (with the relevant series summable). Write $W_k(h) = \sum_{j<k} V_j(h_{<j})$ for the predictable quadratic variation along a history $h \in \alpha^k$. Then for all $v \ge 0$ and $\varepsilon \ge 0$,

$$
\Pr_{h \sim P_n}\Big[\exists k \le n:\ X_k(h_{<k}) \ge X_0 + \varepsilon \text{ and } W_k(h_{<k}) \le v\Big] \le \exp\Big(-\frac{\varepsilon^2}{2(v + b\varepsilon/3)}\Big),
$$

and when $b > 0$ and $v > 0$ the right side may be replaced by Bennett's bound $\exp(-\frac{v}{b^2} h(b\varepsilon/v))$ with $h(u) = (1+u)\ln(1+u) - u$. In particular, if $|X_{k+1}(h,x) - X_k(h)| \le b$ on supported steps and $V_k \equiv v_k$ are deterministic, then $\Pr[X_n \ge X_0 + \varepsilon] \le \exp(-\varepsilon^2/(2(\sum_k v_k + b\varepsilon/3)))$, with the analogous lower and two-sided (factor $2$) bounds for sub- and martingales.

## Proof sketch

For $s \ge 0$, Bennett's one-step bound shows that $\exp\big(s(X_k - X_0) - \frac{e^{sb} - 1 - sb}{b^2} W_k\big)$ is a nonnegative supermartingale along the process with initial value $1$. Ville's maximal inequality bounds the probability that it ever exceeds $\exp(s\varepsilon - \frac{e^{sb}-1-sb}{b^2} v)$, which it does on the event in question. Optimizing $s$ as in Bennett's inequality gives the Poisson form, and the Bernstein form follows from the lower bound on $h$ (with degenerate cases $b = 0$ or $v = 0$ handled by limits).

## Depends on

- [Finite-horizon adaptive discrete process and its supermartingales](finite-horizon-adaptive-discrete-process.md)
- [Bennett's inequality and its Bernstein relaxation](bennett-inequality.md)
- [Ville's maximal inequality](../../hypothesis-testing/sequential-tests-and-quickest-change-detection/anytime-valid-confidence-sequences/ville/ville-maximal-ineq.md)

## Proof depends on

- [Bennett's one-step moment generating function bound](bennett-one-step-mgf-bound.md)
- [Bennett's inequality and its Bernstein relaxation](bennett-inequality.md)
- [Ville's maximal inequality](../../hypothesis-testing/sequential-tests-and-quickest-change-detection/anytime-valid-confidence-sequences/ville/ville-maximal-ineq.md)

## Sources

- D. A. Freedman, "On Tail Probabilities for Martingales", The Annals of Probability 3(1), 1975.
- J. Ville, "Etude critique de la notion de collectif", Gauthier-Villars, 1939.
- G. Bennett, "Probability Inequalities for the Sum of Independent Random Variables", Journal of the American Statistical Association 57, 1962.
