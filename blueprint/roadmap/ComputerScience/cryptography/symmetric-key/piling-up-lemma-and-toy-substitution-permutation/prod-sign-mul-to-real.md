# Prod sign mul to Real

Throughout, $n \in \mathbb{N}$, $p_0, \dots, p_{n-1}$ are probability distributions on $\{\mathrm{false}, \mathrm{true}\}$, and $w$ ranges over the finite set $\mathrm{Bool}^n$ of words $w = (w_0, \dots, w_{n-1})$. With the [sign](../../../../Combinatorics/boolean-functions/kahn-kalai-linial-inequality/walsh-fourier-analysis-on-the-uniform-cube-and-t/khc-sign.md) map $s(\mathrm{false}) = 1$, $s(\mathrm{true}) = -1$, $X(w) = w_0 \oplus \cdots \oplus w_{n-1}$ the [XOR of all bits](../../../../TheoryOfComputation/pseudorandomness-and-one-way-functions/yao-s-xor-lemma/xor-fold.md) and $W(w) = \prod_{i<n} \mathrm{toReal}(p_i(w_i))$, for every word $w$ the per-word signed product factors as

$$
\prod_{i<n} s(w_i) \cdot \mathrm{toReal}\bigl(p_i(w_i)\bigr) = s\bigl(X(w)\bigr) \cdot W(w).
$$
