# PRF-based encryption scheme

Let the key space $K$ and the randomness space $X$ be finite and nonempty, let $Y$ be an additive commutative group, and let $F \colon K \to X \to Y$. The PRF-based private-key encryption scheme with messages in $Y$ and ciphertexts in $X \times Y$ draws a key $k$ uniformly from $K$; to encrypt $m$ it draws $r$ uniformly from $X$ and outputs $(r, F(k, r) + m)$; it decrypts $(r, c)$ to `some` $(c - F(k, r))$, so decryption never fails (Katz and Lindell, Construction 3.30, with XOR replaced by the group addition).
