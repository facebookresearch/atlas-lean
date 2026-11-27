# HQC public-key encryption

Let $\mathcal{R} = \mathbb{F}_2[X]/(X^n - 1)$ with $n$ prime, identified with $\mathbb{F}_2^n$, so multiplication by $h$ is the circulant matrix of $h$. Fix a public code $\mathcal{C}$ of length $n_1 n_2 \le n$ (a concatenated Reed–Muller/Reed–Solomon code) with generator $\mathbf{G}$ and an efficient decoder, and weights $w, w_r, w_e$. HQC-PKE: key generation samples $h \in \mathcal{R}$ uniform and $x, y \in \mathcal{R}$ of Hamming weight $w$, and publishes $(h, s = x + h y)$; the secret key is $y$. To encrypt $m$, sample $r_1, r_2$ of weight $w_r$ and $e$ of weight $w_e$ and output

$$
u = r_1 + h r_2, \qquad v = \mathrm{trunc}\bigl(m\mathbf{G} + s r_2 + e\bigr).
$$

Decryption decodes $v - \mathrm{trunc}(u y) = m\mathbf{G} + \mathrm{trunc}(x r_2 - r_1 y + e)$ with the decoder of $\mathcal{C}$. Security rests on the hardness of decoding random quasi-cyclic codes: distinguishing $(h, x + hy)$ (two blocks) and the three-block syndrome $(h, s, r_1 + hr_2, s r_2 + e)$ from uniform vectors of the same parities (the parity of each syndrome block is determined by $h$, $s$ and the weights).

## Depends on

- [Reed-Solomon code](../../../../../InformationTheory/error-correcting-codes/reed-solomon-codes/code.md)

## Sources

- Philippe Gaborit et al., "Hamming Quasi-Cyclic (HQC)", Version 5.1, November 9, 2026.
