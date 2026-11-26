# Shamir threshold secret sharing

Let $\mathbb{F}$ be a finite field, $m$ parties with distinct nonzero evaluation points $\alpha_1, \dots, \alpha_m \in \mathbb{F}$ (so $|\mathbb{F}| > m$), and a threshold $t < m$. To share $z \in \mathbb{F}$, draw $r_1, \dots, r_t$ uniformly, set $f(X) = z + r_1 X + \dots + r_t X^t$, and give party $i$ the share $f(\alpha_i)$. Any coalition $S$ with $|S| \ge t + 1$ reconstructs $z = f(0) = \sum_{i \in S} \lambda_i^S f(\alpha_i)$ with the Lagrange weights at zero $\lambda_i^S = \prod_{j \in S \setminus\{i\}} \alpha_j / (\alpha_j - \alpha_i)$. This is a secret-sharing scheme with uniform randomness for the threshold access structure, in which exactly the coalitions $S$ with $|S| \ge t+1$ are authorized.

## Sources

- Adi Shamir, "How to Share a Secret", Communications of the ACM, 1979.
- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
