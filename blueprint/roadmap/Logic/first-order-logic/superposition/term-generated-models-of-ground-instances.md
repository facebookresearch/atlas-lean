# Term-generated models of ground instances

A $\Sigma$-interpretation $\mathcal A$ is *term-generated* if every element of its universe is the value of some ground term. Let $N$ be a set of universally quantified $\Sigma$-clauses and $\mathcal A$ a term-generated $\Sigma$-interpretation. Then $\mathcal A$ is a model of the set $G_\Sigma(N)$ of ground instances of $N$ if and only if it is a model of $N$.

**Proof.** A model of $N$ satisfies all instances. Conversely, given values $a_i$ for the variables of a clause $C$ of $N$, choose ground terms $t_i$ denoting them; then $C$ holds under this assignment because $C\{x_i \mapsto t_i\} \in G_\Sigma(N)$ holds.

## Sources

- U. Waldmann, *Automated Reasoning II*, lecture notes, Max Planck Institute for Informatics, summer semester 2024, <https://rg1-teaching.mpi-inf.mpg.de/autrea2-ss24/notes-current.pdf>, Section 3.4, the definition of term-generated interpretations and Lemma 3.10 with its proof, p. 59.
