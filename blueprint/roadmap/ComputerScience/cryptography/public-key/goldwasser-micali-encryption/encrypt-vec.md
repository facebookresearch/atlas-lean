# Bitwise Goldwasser–Micali encryption

An $\ell$-bit message $m$ is encrypted with randomness $x_1, \dots, x_\ell$ (units modulo $N$)
componentwise: the $i$-th ciphertext component is the [encryption of the bit](encrypt-bit.md) $m_i$
with randomness $x_i$.

## Sources

- S. Goldwasser and S. Micali, "Probabilistic encryption & how to play mental poker keeping secret all partial information", Proc. 14th ACM STOC (1982), 365-377, Section 4 (a message $m = (m_1, \dots, m_k)$ is sent as $(e_1, \dots, e_k)$).
