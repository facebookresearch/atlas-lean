# Multicalibration by iterated level-set corrections terminates quickly

Let $\mathcal{X}$ be a finite universe of $N$ individuals, let $p^* \in [0,1]^N$ give each individual's true outcome probability, and let $\mathcal{C} \subseteq 2^{\mathcal{X}}$ be a collection of subpopulations with $|S| \ge \gamma N$ for every $S \in \mathcal{C}$, for some $\gamma \in (0,1]$. A statistical query of tolerance $\tau$ on $S \subseteq \mathcal{X}$ returns a value within $\tau N$ of $p^*_S = \sum_{i \in S} p^*_i$. For $\lambda > 0$ let $\Lambda[0,1] = \{\lambda/2, 3\lambda/2, \dots, 1 - \lambda/2\}$, let $\lambda(v) = [v - \lambda/2, v + \lambda/2)$ (with $[1 - \lambda, 1]$ for the last value), and for a predictor $x \in [0,1]^N$ write $S_v(x) = \{i : x_i \in \lambda(v)\} \cap S$. For $\alpha, \lambda > 0$, the predictor $x$ is **$(\alpha, \lambda)$-multicalibrated** on $\mathcal{C}$ if for every $S \in \mathcal{C}$ and $v \in \Lambda[0,1]$ with $|S_v(x)| \ge \alpha\lambda|S|$,

$$
\Bigl|\sum_{i \in S_v(x)} (x_i - p^*_i)\Bigr| \le \alpha\,|S_v(x)| .
$$

Start from $x = (1/2, \dots, 1/2)$ and make passes over all pairs $S \in \mathcal{C}$, $v \in \Lambda[0,1]$ with $|S_v(x)| \ge \alpha\lambda|S|$. For each, let $\bar v$ be the average of $x$ on $S_v(x)$ and ask a guess-and-check query: it reports agreement when $|p^*_{S_v(x)} - |S_v(x)|\,\bar v| < \alpha|S_v(x)|/2$, it returns an estimate $r$ with $|r\,|S_v(x)| - p^*_{S_v(x)}| \le \alpha|S_v(x)|/4$ when this gap exceeds $\alpha|S_v(x)|$, and it may do either in between; on an estimate, replace $x_i$ by $x_i + (r - \bar v)$, projected onto $[0,1]$, for every $i \in S_v(x)$. Stop after a pass with no estimate. This procedure makes at most $O(1/(\alpha^3 \lambda \gamma))$ updates, each guess-and-check query can be answered by a statistical query of tolerance $\alpha|S_v(x)|/(4N)$, and the result is a statistical query algorithm that learns an $(\alpha, \lambda)$-multicalibrated predictor with respect to $\mathcal{C}$ using $O(|\mathcal{C}|/(\alpha^3 \lambda^2 \gamma))$ queries.

## Proof sketch

On a category $S_v$ of size $\beta N \ge \alpha\lambda\gamma N$ that is updated, the mean gap $\nu$ between $p^*$ and $x$ satisfies $|\nu| \ge \alpha/2$ and the estimation error $\eta$ of the shift satisfies $|\eta| \le \alpha/4$, so expanding the square shows that $\lVert p^* - x \rVert_2^2$ decreases by at least $(\nu^2 + \nu\eta - \eta^2)|S_v| \ge (\alpha/4)^2|S_v| \ge \alpha^3\lambda\gamma N/16$; projection onto $[0,1]$ does not increase it. Since $\lVert p^* - x \rVert_2^2 \le N$ initially, there are at most $16/(\alpha^3\lambda\gamma)$ updates. Each pass inspects at most $|\mathcal{C}|/\lambda$ categories, which bounds the number of queries. When a pass returns no estimate, every category with $|S_v(x)| \ge \alpha\lambda|S|$ has gap at most $\alpha|S_v(x)|$, which is $(\alpha, \lambda)$-multicalibration.

## Depends on

- [Multicalibrated predictors](multicalibrated-predictor.md)

## Proof depends on

- [Each multiaccuracy correction decreases the squared distance to the Bayes predictor](multiaccuracy-correction-potential-decrease.md)

## Sources

- U. Hebert-Johnson, M. P. Kim, O. Reingold, G. N. Rothblum, "Multicalibration: Calibration for the (Computationally-Identifiable) Masses", ICML (2018), arXiv:1711.08513, Definitions 2.4, 2.8 and 2.9, Algorithm 3.2, Lemma 3.6 and Theorem 3.7.
