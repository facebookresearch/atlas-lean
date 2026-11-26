# Diffie–Hellman oblivious pseudorandom functions

Let $\mathbb{G}$ be a cyclic group of prime order $q$ with generator $g$, $H : X \to \mathbb{G}$ and $H' : X \times \mathbb{G} \to Y$ hash functions. The *Diffie–Hellman PRF* is $F'(k, x) = H'(x, H(x)^k)$ with key $k \in \mathbb{Z}_q$. An *oblivious PRF protocol* lets a receiver with input $x$ learn $F'(k, x)$ from a sender holding $k$ while the sender learns nothing about $x$. In the blinded-exponentiation protocol (2HashDH) the receiver sends $v = H(x)^\rho$ for uniform $\rho \in \mathbb{Z}_q^*$, the sender returns $w = v^k$, and the receiver outputs $H'(x, w^{1/\rho})$.

## Depends on

- [DDH advantage of the distinguisher built from a CDH solver](../../../public-key/hardness-assumptions/ddh-advantage-ddh-of-cdh.md)

## Sources

- S. Jarecki, A. Kiayias, H. Krawczyk and J. Xu, "Highly-Efficient and Composable Password-Protected Secret Sharing (Or: How to Protect Your Bitcoin Wallet Online)", IEEE European Symposium on Security and Privacy (EuroS&P), 2016, pp. 276-291 (the 2HashDH PRF $f_k(x) = H_2(x, H_1(x)^k)$ and its blinded evaluation protocol).
