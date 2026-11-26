# Ladder Cramér identity

Let $X_0, X_1, \dots$ be i.i.d. integer-valued random variables on a probability space that are not almost surely $0$, with score walk $S_n = X_0 + \dots + X_{n-1}$, first strict ascending ladder epoch $\tau_+$ and defective ladder-height law $g_j = \mathbb{P}(\tau_+ < \infty, S_{\tau_+} = j)$. If $\theta > 0$ solves $\mathbb{E}[e^{\theta X_0}] = 1$, then $\sum_j g_j e^{\theta j} = 1$.

The proof stops the martingale $e^{\theta S_n}$ at $\tau_+ \wedge n$ and bounds the remainder $\mathbb{E}[e^{\theta S_n}; \tau_+ > n] \le (\mathbb{E}[e^{\theta X_0/2}])^n \to 0$.
