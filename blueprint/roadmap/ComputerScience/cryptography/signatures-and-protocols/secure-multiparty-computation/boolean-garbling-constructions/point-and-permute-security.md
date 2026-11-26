# Point-and-permute garbling is correct and simulation private from a PRF

Point-and-permute garbling over conventional Boolean circuits is a valid garbling scheme: for every circuit, coins and input, decoding the evaluation of the encoded input gives the circuit's output; garbling, encoding, evaluation and decoding run in polynomial time. If the pad function is a pseudorandom function family, the scheme is prv.sim secure with topology side information $\Phi_{\mathrm{topo}}$: one universal polynomial-time simulator, which garbles the topology with random tables except for the active rows and fixes the output permute bits to the given output, makes every probabilistic polynomial-time adversary's advantage negligible. Concretely, for each instance the advantage is bounded by a sum over gates of PRF advantages (a hybrid over the inactive labels in topological order).

## Proof sketch

In topological order replace the PRF keyed by the inactive label of each wire by a random function; since inactive labels are used only to encrypt inactive rows, those rows become uniform, and the remaining view is produced by the simulator from the topology and output alone.

## Depends on

- [Point-and-permute garbling](point-and-permute-garbling.md)
- [Side-information functions and privacy notions for garbling schemes](../garbling-scheme-security/garbling-privacy-notions.md)

## Proof depends on

- [Indistinguishability versus simulation privacy of garbling schemes](../garbling-scheme-security/garbling-ind-versus-sim.md)
- [Hybrid argument](../../../security-games/games-and-advantages/advantage-le-sum.md)

## Sources

- Mihir Bellare, Viet Tung Hoang and Phillip Rogaway, "Foundations of Garbled Circuits", Proceedings of the 2012 ACM Conference on Computer and Communications Security, 2012.
- Donald Beaver, Silvio Micali and Phillip Rogaway, "The Round Complexity of Secure Protocols", Proceedings of the 22nd Annual ACM Symposium on Theory of Computing, 1990.
