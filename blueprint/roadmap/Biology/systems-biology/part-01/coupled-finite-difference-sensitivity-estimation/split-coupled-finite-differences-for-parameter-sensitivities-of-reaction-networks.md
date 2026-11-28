# Split-coupled finite differences for parameter sensitivities of reaction networks

**Setting.** A stochastic reaction network (or any continuous-time Markov chain with finitely many jump directions $\zeta_k$) with parameter $\theta$ is written in random time-change form

$$
X^\theta(t)=X^\theta(0)+\sum_{k=1}^MY_k\Big(\int_0^t\lambda^\theta_k(X^\theta(s))\,ds\Big)\zeta_k,
$$

with independent unit-rate Poisson processes $Y_k$ and intensities $\lambda_k^\theta$. The goal is $\frac{d}{d\theta}\mathbb E f(X^\theta(T))$, estimated by the finite difference $\epsilon^{-1}\big(f(X^{\theta+\epsilon}(T))-f(X^\theta(T))\big)$ averaged over $R$ paired simulations. Assume (A1) the $\lambda_k^\theta$ and $F^\theta=\sum_k\lambda_k^\theta\zeta_k$ are Lipschitz in the state uniformly in $\theta$, and (A2) $\sup_x|\lambda_k^{\theta+\epsilon}(x)-\lambda_k^\theta(x)|+|F^{\theta+\epsilon}(x)-F^\theta(x)|\le K_2\epsilon$.

**Coupling (split coupling).** Let $m_k(s)=\lambda_k^{\theta+\epsilon}(X^{\theta+\epsilon}(s))\wedge\lambda_k^\theta(X^\theta(s))$ and use three independent unit Poisson processes per reaction:

$$
\begin{aligned}
X^{\theta+\epsilon}(t)&=X(0)+\sum_kY_{k,1}\Big(\int_0^tm_k\Big)\zeta_k+\sum_kY_{k,2}\Big(\int_0^t\big[\lambda_k^{\theta+\epsilon}(X^{\theta+\epsilon})-m_k\big]\Big)\zeta_k,\\
X^\theta(t)&=X(0)+\sum_kY_{k,1}\Big(\int_0^tm_k\Big)\zeta_k+\sum_kY_{k,3}\Big(\int_0^t\big[\lambda_k^\theta(X^\theta)-m_k\big]\Big)\zeta_k .
\end{aligned}
$$

The pair is a single Markov chain on an enlarged state space and can be simulated by a next-reaction-type algorithm with $3M$ channels.

**Theorem.** Under (A1)–(A2), for every $T>0$ and every $C^1$ function $f$ with bounded first derivative on the state space, there are constants such that

$$
\mathbb E\sup_{t\le T}|X^{\theta+\epsilon}(t)-X^\theta(t)|\le C\epsilon,\qquad
\mathbb E\sup_{t\le T}|X^{\theta+\epsilon}(t)-X^\theta(t)|^2\le C\epsilon,\qquad
\mathbb E\sup_{t\le T}\big(f(X^{\theta+\epsilon}(t))-f(X^\theta(t))\big)^2\le C_{T,f}\,\epsilon .
$$

Hence the variance of the coupled finite-difference estimator is $O(\epsilon^{-1})$ per path, compared with $O(\epsilon^{-2})$ for independent simulation of the two processes. Both rates are sharp: for $\emptyset\xrightarrow{\theta}S$ the difference is exactly a Poisson process $Y_2(\epsilon t)$.

## Expansion

The shared stream $Y_{k,1}$ fires reactions in both copies simultaneously at the common rate $m_k$, and only the small excess intensities, of size $O(\epsilon)$ by (A2) plus $O(|X^{\theta+\epsilon}-X^\theta|)$ by (A1), drive the copies apart. Because the centered counting processes are martingales in the natural filtration, the first two moments of the gap satisfy Gronwall inequalities whose forcing is $O(\epsilon)$; the second moment is also $O(\epsilon)$ because a jump of size $|\zeta_k|$ squared is still of size $|\zeta_k|$ times its probability. The common-reaction-path coupling, which uses the same $Y_k$ in both copies, lacks this martingale structure and its variance can grow with the number of reaction events (as in the mRNA birth–death model $\emptyset\rightleftarrows M$); in examples such as gene expression and a genetic toggle switch the split coupling usually gives substantially lower variance, though not universally. Coupling even tighter, by reusing one Poisson process for both excess channels $Y_{k,2}$ and $Y_{k,3}$, is wrong: it biases the estimator, e.g. for $X\xrightarrow{\theta}\emptyset$ with $X_0=1$ the centered difference converges to $0$ instead of $\frac{d}{d\theta}\mathbb EX^\theta(1)|_{\theta=1}=-e^{-1}$.

## Depends on

- [Gillespie direct method (stochastic simulation algorithm)](../gillespie-direct-method.md)

## Proof depends on

- [Gronwall inequality in integral form](../../../../Analysis/ordinary-differential-equations/gronwall-inequality/gronwall-inequality-integral-form.md)

## Sources

- David F. Anderson, "An Efficient Finite Difference Method for Parameter Sensitivities of Continuous Time Markov Chains", arXiv:1109.2890 (2011), Section 2 (Assumptions 1–2), Section 3 (coupling and Algorithm 1, Examples 1–3, Theorem 1, Lemmas 2–3), Section 4 (numerical examples), <https://doi.org/10.48550/arXiv.1109.2890>.
