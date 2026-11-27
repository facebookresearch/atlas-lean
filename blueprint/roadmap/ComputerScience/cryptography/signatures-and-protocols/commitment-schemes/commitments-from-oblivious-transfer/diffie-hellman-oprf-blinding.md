# Correctness and blinding of the blinded-exponentiation Diffie–Hellman OPRF protocol

In the blinded-exponentiation Diffie–Hellman OPRF protocol over a group $\mathbb{G}$ of prime order $q$: (i) *correctness*: if the sender answers $v$ honestly with $v^k$, the receiver's unblinded group element is $(H(x)^{\rho k})^{1/\rho} = H(x)^k$, so it outputs $F'(k, x)$; (ii) *receiver privacy of the message*: if $H(x) \ne 1$, then for uniform $\rho \in \mathbb{Z}_q^*$ the message $H(x)^\rho$ is uniform on $\mathbb{G} \setminus \{1\}$; in particular its distribution is the same for all inputs $x$ with $H(x) \ne 1$.

## Proof sketch

(i) is exponent arithmetic in a group of prime order. (ii) Every non-identity element of a group of prime order generates it, so for $h \ne 1$ the map $\rho \mapsto h^\rho$ is a bijection from $\mathbb{Z}_q^*$ onto $\mathbb{G} \setminus \{1\}$ and carries the uniform law to the uniform law.

## Depends on

- [Diffie–Hellman oblivious pseudorandom functions](diffie-hellman-oprf.md)

## Sources

- S. Jarecki, A. Kiayias, H. Krawczyk and J. Xu, "Highly-Efficient and Composable Password-Protected Secret Sharing (Or: How to Protect Your Bitcoin Wallet Online)", IEEE European Symposium on Security and Privacy (EuroS&P), 2016, pp. 276-291 (the 2HashDH protocol and its unblinding identity $H_2(x, b^{1/r}) = H_2(x, H_1(x)^k)$).
- V. Shoup, "A Computational Introduction to Number Theory and Algebra", 2nd ed., Cambridge University Press, 2009, Theorem 6.33 and its proof (every non-identity element of a group of prime order generates it).
