# Sampling expectation of a product factorizes

For every natural number $n$, all functions $g_1, \dots, g_n : \{0, 1\} \to \mathbb{R}$ and every $q \in \mathbb{R}^n$, the [sampling expectation](sample-expect.md) satisfies

$$\mathbb{E}_q\Bigl[x \mapsto \prod_{i=1}^{n} g_i(x_i)\Bigr] = \prod_{i=1}^{n} \bigl(g_i(1)\, q_i + g_i(0)\, (1 - q_i)\bigr).$$
