# ModRaise introduces a small integer multiple of the base modulus

Let $\mathbf{c}=(b,a)$ be a level-$0$ ciphertext, where $b,a$ have coefficients in $(-q_0/2,q_0/2]$ and $s$ has coefficients in $\{-1,0,1\}$ with Hamming weight $h$, and let $m=[b+as]_{q_0}$ be its *centered noisy decryption*, the unique polynomial congruent to $b+as$ modulo $q_0$ with coefficients in $(-q_0/2,q_0/2]$ (message plus error). A mere congruence $b+as\equiv m\pmod{q_0}$ would not do: replacing $m$ by $m+q_0$ preserves it but changes the quotient below. Computing $t=b+as$ over the integers (in $\mathbb{Z}[X]/(X^{N}+1)$) gives $t=m+q_0I$ for an integer polynomial $I$ with $\|I\|_\infty\le(h+1)/2+1$; heuristically $\|I\|_\infty=O(\sqrt{h})$. Viewing $\mathbf{c}$ modulo a larger $Q$ (ModRaise), $b+as\equiv m+q_0I\pmod Q$, so $\mathbf{c}$ encrypts $t$ modulo $Q$ when $\|t\|_\infty<Q/2$. Thus bootstrapping must homomorphically remove the term $q_0I$, i.e., evaluate the coefficientwise reduction $t\mapsto t\bmod q_0$ on inputs of the form $m+q_0I$ with $|m|\ll q_0$.

## Proof sketch

Over the integers, $b+as$ has coefficients bounded by $(q_0/2)(1+h)$, since each coefficient of $as$ is a signed sum of $h$ coefficients of $a$. Its difference with the centered representative $m$, whose coefficients have absolute value at most $q_0/2$, is a multiple of $q_0$, so the quotient $I$ has coefficients of absolute value at most $(1+h)/2+1/2$. The heuristic bound models each coefficient of $t/q_0$ as a sum of $h+1$ independent uniform variables on $(-\tfrac12,\tfrac12)$.

## Depends on

- [CKKS ciphertexts and approximate decryption](ckks-ciphertexts.md)

## Sources

- Jung Hee Cheon, Kyoohyung Han, Andrey Kim, Miran Kim, Yongsoo Song, "Bootstrapping for Approximate Homomorphic Encryption", EUROCRYPT (2018), §§5.1 and 5.3.
