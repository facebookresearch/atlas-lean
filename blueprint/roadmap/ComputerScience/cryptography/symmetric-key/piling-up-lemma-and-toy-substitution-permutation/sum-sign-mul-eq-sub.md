# Sum sign mul eq sub

Throughout, $n \in \mathbb{N}$, $p_0, \dots, p_{n-1}$ are probability distributions on $\{\mathrm{false}, \mathrm{true}\}$, and $w$ ranges over the finite set $\mathrm{Bool}^n$ of words $w = (w_0, \dots, w_{n-1})$. With the [sign](../../../../Combinatorics/boolean-functions/kahn-kalai-linial-inequality/walsh-fourier-analysis-on-the-uniform-cube-and-t/khc-sign.md) map $s(\mathrm{false}) = 1$, $s(\mathrm{true}) = -1$, $X(w) = w_0 \oplus \cdots \oplus w_{n-1}$ the [XOR of all bits](../../../../TheoryOfComputation/pseudorandomness-and-one-way-functions/yao-s-xor-lemma/xor-fold.md) and $W(w) = \prod_{i<n} \mathrm{toReal}(p_i(w_i))$, the signed sum over all words is the sum of $W$ over the **false** fiber minus the sum over the **true** fiber:

$$
\sum_{w \in \mathrm{Bool}^n} s\bigl(X(w)\bigr) \cdot W(w) = \sum_{X(w) = \mathrm{false}} W(w) - \sum_{X(w) = \mathrm{true}} W(w).
$$

Reversing the order of the two fiber sums changes the sign of the result.
