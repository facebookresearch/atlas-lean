# Stochastic linear bandits and LinUCB regret

This node covers the stochastic linear bandit model, the LinUCB policy, the confidence ellipsoid of regularized
least squares and the regret of LinUCB; the elliptical potential bounds used in the regret proof are results of their own.

## Proof depends on

- [Elliptical potential lemma](elliptical-potential-lemma.md)

## Expansion

A sound expansion has separate pages for:

1. **Model.** In round $t$ the learner is given a nonempty compact action set $\mathcal{A}_t \subseteq \mathbb{R}^d$ (finite sets
   included), chooses $A_t \in \mathcal{A}_t$ and receives the reward $X_t = \langle \theta^*, A_t \rangle + \eta_t$, for a fixed unknown
   $\theta^* \in \mathbb{R}^d$. The noise is conditionally 1-sub-Gaussian: $\mathbb{E}[\exp(\alpha \eta_t) \mid \mathcal{F}_{t-1}] \le \exp(\alpha^2/2)$ for all
   $\alpha \in \mathbb{R}$, for a filtration $(\mathcal{F}_t)$ such that $A_1, X_1, \dots, A_{t-1}, X_{t-1}, A_t$ are $\mathcal{F}_{t-1}$-measurable (Eq. (20.4)).
   Parameters: $d \ge 1$, a horizon $n \ge 1$, $L \ge 0$ with $\lVert a \rVert_2 \le L$ for all $a \in \mathcal{A}_t$ and $t \le n$, and
   $m_2 \ge 0$ with $\lVert \theta^* \rVert_2 \le m_2$. Compactness is an added hypothesis, a special case of the source's setting: it
   makes every maximum below attained, which the source takes for granted.
2. **LinUCB policy.** For a regularization parameter $\lambda > 0$, let $V_0 = \lambda I$, $V_t = V_0 + \sum_{s \le t} A_s A_s^{\mathsf T}$ and
   $\hat\theta_t = V_t^{-1} \sum_{s \le t} A_s X_s$, so that $\hat\theta_0 = 0$. In round $t$ let $C_t \subseteq \mathbb{R}^d$ be a nonempty closed confidence
   set, determined by $A_1, X_1, \dots, A_{t-1}, X_{t-1}$ and contained in the ellipsoid
   $E_t = \{\theta : \lVert \theta - \hat\theta_{t-1} \rVert_{V_{t-1}}^2 \le \beta_t\}$, where $1 \le \beta_1 \le \beta_2 \le \dots$ and each $\beta_t$ is a constant
   (Eqs. (19.5)–(19.7)) or, as in Eq. (19.14), determined by $A_1, \dots, A_{t-1}$. LinUCB plays a maximizer
   $A_t \in \operatorname{argmax}_{a \in \mathcal{A}_t} \mathrm{UCB}_t(a)$ of $\mathrm{UCB}_t(a) = \max_{\theta \in C_t} \langle \theta, a \rangle$, chosen so that $A_t$ is
   $\mathcal{F}_{t-1}$-measurable, for instance by a fixed tie-breaking rule when $\mathcal{A}_t$ is finite; in general such a choice is
   assumed (Eqs. (19.2) and (19.3)). Both maxima are attained: the inner one as $C_t$ is closed and lies in the
   bounded set $E_t$ (as $V_{t-1} \succeq \lambda I$), and the outer one as $\mathrm{UCB}_t$, the support function of the nonempty compact set
   $C_t$, is continuous and $\mathcal{A}_t$ is nonempty and compact.
3. **Confidence ellipsoid.** For $\delta \in (0, 1)$, with probability at least $1 - \delta$, for all $t \le n$,
   $\lVert \theta^* - \hat\theta_{t-1} \rVert_{V_{t-1}} < r_t$, where $r_t = \sqrt{\lambda}\, m_2 + \sqrt{2\log(1/\delta) + \log(\det V_{t-1} / \lambda^d)}$
   (Theorem 20.5, under the assumptions of item 1, whatever the actions, as long as each $A_t$ is $\mathcal{F}_{t-1}$-measurable). The radius $r_t$ is nondecreasing in $t$, as
   $\det V_t \ge \det V_{t-1}$, and for $t \le n$ it is at most $\bar\beta_n^{1/2}$, where
   $\bar\beta_n^{1/2} = \sqrt{\lambda}\, m_2 + \sqrt{2\log(1/\delta) + d \log((d\lambda + nL^2)/(d\lambda))}$ is the value of Eq. (19.8), by the
   determinant–trace inequality and $\lVert A_s \rVert_2 \le L$.
4. **LinUCB regret.** For the LinUCB policy of item 2, under Assumption 19.1 of the source, namely (a) $1 \le \beta_1 \le \dots \le \beta_n$,
   (b) $\langle \theta^*, a - b \rangle \le 1$ for all $a, b \in \mathcal{A}_t$ and $t \le n$, (c) $\lVert a \rVert_2 \le L$ for all such $a$, and (d) for some
   $\delta \in (0, 1)$, with probability at least $1 - \delta$, $\theta^* \in C_t$ for all $t \le n$, the pseudo-regret
   $\hat R_n = \sum_{t \le n} \max_{a \in \mathcal{A}_t} \langle \theta^*, a - A_t \rangle$ satisfies, with probability at least $1 - \delta$,
   $\hat R_n \le \sqrt{8 d n \beta_n \log((d\lambda + nL^2)/(d\lambda))}$ (Theorem 19.2), with $\beta_n$ that of item 2. Item 3 provides (a)
   and (d) for $C_t = E_t$ with either $\beta_t = \max(1, r_t^2)$, which is nondecreasing, at least $1$ and determined by
   $A_1, \dots, A_{t-1}$ (Eq. (19.14) with a floor at $1$), or the constant $\beta_t = \max(1, \bar\beta_n)$ for $t \le n$; in both cases
   $\beta_n \le \max(1, \bar\beta_n)$. With $\delta = 1/n$ (so $n \ge 2$), $\bar\beta_n \ge 2 \log 2 > 1$, so the constant choice is $\beta_t = \bar\beta_n$ of
   Eq. (19.8); for it, the expected regret is $O(d \sqrt n \log n)$ as $n \to \infty$ for fixed $\lambda$, $m_2$ and $L$, with a constant that
   depends on $\lambda$, $m_2$ and $L$ (Corollary 19.3, whose O-form suppresses that dependence; see Exercise 19.7(d) and
   Eq. (19.16)).

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Section 19.2 with Eqs. (19.2), (19.3) and (19.5)–(19.7), Assumption 19.1, Theorem 19.2, Eq. (19.8), Corollary 19.3, Lemma 19.4, Note 3 of Section 19.4 with Eq. (19.14), Exercise 19.7(d) with Eq. (19.16), Eq. (20.4) and Theorem 20.5. <https://tor-lattimore.com/downloads/book/book.pdf>
