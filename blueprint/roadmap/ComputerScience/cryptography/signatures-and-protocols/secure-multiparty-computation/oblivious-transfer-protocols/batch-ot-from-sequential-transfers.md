# Batched oblivious transfer from sequential single transfers

Running $k$ single 1-out-of-2 transfers sequentially realizes the batched transfer of $k$ values: in the single-transfer hybrid model the execution is deterministic and correct, and it is perfectly semi-honest private against every coalition with a simulator that splits the coalition's batched output into its $k$ parts. When the single transfer is replaced by a protocol with simulators, the semi-honest advantage against the batched protocol (and against any outer protocol using it) is at most the sum over the $k$ rounds of the expected advantage of the round distinguishers against the single-transfer protocol.

## Proof sketch

Perfect privacy in the hybrid model is immediate because the coalition's view consists of oracle answers that are exactly its outputs. The concrete bound is the composition theorem with a hybrid over the oracle rounds.

## Depends on

- [Ideal 1-out-of-2, batched and 1-out-of-4 oblivious transfer](oblivious-transfer-functionalities.md)

## Proof depends on

- [Composition theorem for semi-honest multiparty protocols](../semi-honest-mpc-foundations/semi-honest-composition-theorem.md)

## Sources

- Oded Goldreich, "Foundations of Cryptography, Volume 2: Basic Applications", Cambridge University Press, 2004.
