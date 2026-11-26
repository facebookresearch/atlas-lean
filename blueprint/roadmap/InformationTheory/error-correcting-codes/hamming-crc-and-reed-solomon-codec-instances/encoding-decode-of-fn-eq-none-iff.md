# When the Reed–Solomon codec fails

For the [Reed–Solomon codec](encoding-3.md) (distinct points $\alpha_1, \dots, \alpha_n$, $k \le n$, a sound and complete key-equation solver for radius $\lfloor (n - k)/2 \rfloor$) and every word $y \in F^n$, decoding $y$ fails exactly when, for every polynomial $p$ of degree less than $k$, the Hamming distance from $y$ to $(p(\alpha_1), \dots, p(\alpha_n))$ exceeds $\lfloor (n - k)/2 \rfloor$.
