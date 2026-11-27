# Point-and-permute garbling

In *point-and-permute* garbling of a Boolean circuit, each wire $i$ carries two random labels $W_i^0, W_i^1 \in \{0,1\}^k$ and a random *permute bit* $\pi_i$; the label $W_i^v$ carries the public *colour* $v \oplus \pi_i$. For a gate $g$ with inputs $a, b$ and output $c$, the garbled table has four rows indexed by colours $(\alpha, \beta)$; row $(\alpha, \beta)$ encrypts the output label (and its colour) for the input values $v_a = \alpha\oplus\pi_a$, $v_b = \beta\oplus\pi_b$ under a pad derived from a pseudorandom function: $F(W_a^{v_a}, g\Vert\alpha\beta) \oplus F(W_b^{v_b}, g\Vert\alpha\beta) \oplus (W_c^{g(v_a, v_b)} \Vert \text{colour})$. The evaluator holding one label per wire decrypts the row given by the colours. Input encoding gives the labels of the input bits and decoding reveals the permute bits of output wires.

## Depends on

- [Garbling schemes and Yao's construction](../garbled-circuits-and-the-correctness-of-yao-s.md)

## Sources

- Donald Beaver, Silvio Micali and Phillip Rogaway, "The Round Complexity of Secure Protocols", Proceedings of the 22nd Annual ACM Symposium on Theory of Computing, 1990.
- Andrew Chi-Chih Yao, "How to Generate and Exchange Secrets", Proceedings of the 27th Annual Symposium on Foundations of Computer Science, 1986.
- Mihir Bellare, Viet Tung Hoang and Phillip Rogaway, "Foundations of Garbled Circuits", Proceedings of the 2012 ACM Conference on Computer and Communications Security, 2012.
