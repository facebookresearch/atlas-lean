# ModRaise introduces a small integer multiple of the base modulus

Let $\mathbf{c}=(b,a)$ be a level-$0$ ciphertext with $b+as\equiv m\pmod{q_0}$, where $b,a$ have coefficients in $(-q_0/2,q_0/2]$ and $s$ has coefficients in $\{-1,0,1\}$ with Hamming weight $h$. Viewing $\mathbf{c}$ modulo a larger $Q$ (ModRaise), $b+as\equiv m+q_0I\pmod Q$ for an integer polynomial $I$ with $\|I\|_\infty\le(h+1)/2+1$; heuristically $\|I\|_\infty=O(\sqrt{h})$. Thus bootstrapping must homomorphically remove the term $q_0I$, i.e., evaluate the coefficientwise reduction $t\mapsto t\bmod q_0$ on inputs of the form $m+q_0I$ with $|m|\ll q_0$.

## Proof sketch

Over the integers, $b+as$ has coefficients bounded by $(q_0/2)(1+h)$, since each coefficient of $as$ is a signed sum of $h$ coefficients of $a$. Its difference with the centered $m$ is a multiple of $q_0$, so the quotient $I$ has coefficients of absolute value at most $(1+h)/2$ plus one for the rounding of $m$.

## Depends on

- [CKKS ciphertexts and approximate decryption](ckks-ciphertexts.md)

## Proof depends on

- [CKKS ciphertexts and approximate decryption](ckks-ciphertexts.md)

## Sources

- Jung Hee Cheon, Kyoohyung Han, Andrey Kim, Miran Kim, Yongsoo Song, "Bootstrapping for Approximate Homomorphic Encryption", EUROCRYPT (2018).
