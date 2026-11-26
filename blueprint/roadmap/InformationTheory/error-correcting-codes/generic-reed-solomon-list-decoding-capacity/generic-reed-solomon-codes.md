# Generic and randomly punctured Reed-Solomon codes

For a field $\mathbb{F}$ and evaluation points $\alpha = (\alpha_1, \dots, \alpha_n)$, $\mathrm{RS}_k(\alpha) = \{(f(\alpha_1), \dots, f(\alpha_n)) : f \in \mathbb{F}[x], \deg f < k\}$. A property holds for *generic* Reed-Solomon codes if it holds for $\mathrm{RS}_k(\alpha)$ for all $\alpha$ outside a proper Zariski-closed subset of $\mathbb{F}^n$ (equivalently, over the field of rational functions with $\alpha_i$ independent indeterminates). A *randomly punctured* RS code over $\mathbb{F}_q$ uses $\alpha$ uniformly random among $n$-tuples of distinct field elements.

## Depends on

- [Reed-Solomon code](../reed-solomon-codes/code.md)

## Sources

- Joshua Brakensiek, Sivakanth Gopi, Visu Makam, "Generic Reed-Solomon codes achieve list-decoding capacity", STOC (2023), SIAM Journal on Computing (2024); arXiv:2206.05256.
- Zeyu Guo, Zihan Zhang, "Randomly punctured Reed-Solomon codes achieve the list decoding capacity over polynomial-size alphabets", FOCS (2023); arXiv:2304.01403.
