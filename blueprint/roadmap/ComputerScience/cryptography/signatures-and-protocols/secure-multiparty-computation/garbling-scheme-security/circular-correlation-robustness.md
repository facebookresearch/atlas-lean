# Circular correlation robust hash functions

Let $L$ be a finite abelian group of labels (for Boolean garbling, one in which every element has order dividing $2$; for arithmetic garbling, a module over a finite commutative ring $R$), let $M$ be a finite abelian group, and let $H : L \times \mathcal{T} \to M$ be a tweakable hash. For a secret offset $\Delta \in L$ drawn from a key distribution, the *circular correlation oracle* answers a query $(x, t, b)$ by $H(x + \Delta, t) + b\cdot\Delta'$, where $\Delta'$ is an output offset determined by $\Delta$. $H$ is *circular correlation robust* (CCR) if no efficient adversary that never repeats a tweak with different queries $x$ and never queries both $(x, t, 0)$ and $(x, t, 1)$ can distinguish this oracle from a random function of $(x, t, b)$ with consistent answers on repeated queries; the advantage is the distinguishing advantage. CCR is the assumption under which Free-XOR and half-gates garbling are proved secure; it is implied by modelling $H$ as a random oracle.

## Depends on

- [Distinguishing advantage](../../../security-games/games-and-advantages/advantage.md)
- [The random oracle model](../../../public-key/random-oracle-constructions/the-random-oracle-model.md)

## Sources

- Seung Geol Choi, Jonathan Katz, Ranjit Kumaresan and Hong-Sheng Zhou, "On the Security of the ``Free-XOR'' Technique", Theory of Cryptography, 2012.
- Samee Zahur, Mike Rosulek and David Evans, "Two Halves Make a Whole: Reducing Data Transfer in Garbled Circuits Using Half Gates", Advances in Cryptology – EUROCRYPT 2015, 2015.
