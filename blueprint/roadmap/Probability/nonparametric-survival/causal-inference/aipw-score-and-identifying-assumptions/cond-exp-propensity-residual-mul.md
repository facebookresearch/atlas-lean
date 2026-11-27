# Correct propensity: the augmentation has conditional mean zero

Let $\mu$ be a finite measure on $\Omega$, $X : \Omega \to \mathcal{X}$ measurable, and write $\mathbb{E}[\,\cdot \mid X]$ for conditional expectation given $\sigma(X)$. Let $T \subseteq \Omega$ be measurable, $e, h : \mathcal{X} \to \mathbb{R}$ measurable with $\lvert h(x) \rvert \le C$ for every $x$. If the propensity is correct, $\mathbb{E}[\mathbf{1}_T \mid X] = e(X)$ $\mu$-a.e., then

$$\mathbb{E}\bigl[(\mathbf{1}_T - e(X))\, h(X) \mid X\bigr] = 0 \quad \mu\text{-a.e.}$$

Where $e(x) \notin \{0, 1\}$, with $h = m_1/e + m_0/(1 - e)$ this is the augmentation term of the AIPW score; where $e(x) \in \{0, 1\}$ the score is not the inverse-weighted contrast minus this term.
