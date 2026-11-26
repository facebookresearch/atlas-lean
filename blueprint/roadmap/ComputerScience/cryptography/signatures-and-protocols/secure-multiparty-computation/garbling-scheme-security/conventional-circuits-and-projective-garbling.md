# Conventional circuits and projective garbling

A *conventional circuit* is a tuple $f = (n, m, q, A, B, G)$ with $n$ input wires, $q$ gates and $m$ output wires (the last $m$ of the $n + q$ wires); gate $g$ reads wires $A(g) < B(g) < g$ and computes the binary function $G_g$, and no gate reads an output wire. Its *topology* is $(n, m, q, A, B)$, and its semantics $\mathrm{ev}(f, x)$ is computed wire by wire in polynomial time. A garbling scheme is *projective* if the input encoding $\mathrm{En}(e, x)$ is the concatenation of tokens $X_i^{x_i}$, one per input bit, where $e$ lists a pair of tokens $(X_i^0, X_i^1)$ of equal length for each input wire; projective schemes are the ones usable in Yao's protocol with oblivious transfer of the tokens.

## Depends on

- [Garbling schemes and Yao's construction](../garbled-circuits-and-the-correctness-of-yao-s.md)

## Sources

- Mihir Bellare, Viet Tung Hoang and Phillip Rogaway, "Foundations of Garbled Circuits", Proceedings of the 2012 ACM Conference on Computer and Communications Security, 2012.
