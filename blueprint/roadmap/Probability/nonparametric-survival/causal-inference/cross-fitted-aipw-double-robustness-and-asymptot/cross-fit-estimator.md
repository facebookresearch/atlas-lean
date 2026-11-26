# Cross Fit Estimator

Let $K \in \mathbb{N}$ and let $\mathrm{fold} : \mathbb{N} \to \mathbb{N} \to \{0, \dots, K-1\}$ be a fold assignment, $\mathrm{fold}(n, i)$ being the fold of unit $i$ at sample size $n$. Let $W_i : \Omega \to \mathcal{W}$ be observations, write $U_{n,k}(\omega) = (W_i(\omega))_{i \in \mathrm{trainFold}(n,k)}$ for the training data of fold $k$, and let $G_{n,k}(u, w)$ be the score of an observation $w$ at the nuisances fitted on training data $u$ of fold $k$. The cross-fitted estimator is

$$\hat\theta_n(\omega) = n^{-1} \sum_{i=0}^{n-1} G_{n, \mathrm{fold}(n,i)}\bigl(U_{n, \mathrm{fold}(n,i)}(\omega), W_i(\omega)\bigr),$$

with $n^{-1} = 0$ at $n = 0$. Each unit is scored at the nuisances fitted on its own fold's training data, which excludes it. For AIPW, $G_{n,k}(u, \cdot)$ is the AIPW score at fitted nuisances $\hat e(u), \hat g_0(u), \hat g_1(u)$.
