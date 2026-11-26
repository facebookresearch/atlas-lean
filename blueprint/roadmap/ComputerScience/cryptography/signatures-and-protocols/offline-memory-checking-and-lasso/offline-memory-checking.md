# Offline memory checking with timestamps

Consider a memory of $M$ cells accessed by a sequence of operations, each reading a value $v$ from address $a$ and writing back $v'$. In *offline memory checking*, each cell stores a triple (address, value, timestamp). Define multisets of triples: $\mathsf{Init}=\{(a,v_a^{0},0)\}_a$, $\mathsf{RS}$ the read set of triples $(a,v,t)$ returned by reads, $\mathsf{WS}$ the write set of triples $(a,v',t')$ with $t'$ greater than the read timestamp (e.g., a global counter), and $\mathsf{Final}=\{(a,v_a^{\mathrm{fin}},t_a^{\mathrm{fin}})\}_a$. The checker accepts iff $\mathsf{Init}\cup\mathsf{WS}=\mathsf{RS}\cup\mathsf{Final}$ as multisets.

## Sources

- Manuel Blum, Will Evans, Peter Gemmell, Sampath Kannan, Moni Naor, "Checking the Correctness of Memories", Algorithmica (1994).
- Srinath Setty, "Spartan: Efficient and General-Purpose zkSNARKs without Trusted Setup", CRYPTO (2020), IACR ePrint 2019/550.
