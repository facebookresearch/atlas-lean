# Control-flow graphs of machine code

Let $M_c$ be a code memory of the [machine under attack](machine-code-under-attack.md). A graph $G$ on addresses with successor sets $\mathrm{succ}(w) \subseteq \mathrm{dom}(M_c)$ is a
*control-flow graph* (CFG) for $M_c$ if

1. $\mathrm{succ}(w) = \{w + 1\} \cap \mathrm{dom}(M_c)$ when $M_c(w)$ is a $\mathbf{label}$, $\mathbf{add}$, $\mathbf{addi}$, $\mathbf{movi}$, $\mathbf{ld}$ or $\mathbf{st}$ instruction;
2. $\mathrm{succ}(w) = \{w + 1, w'\} \cap \mathrm{dom}(M_c)$ when $M_c(w)$ is $\mathbf{bgt}\ r_s, r_t, w'$;
3. $\mathrm{succ}(w) = \{w'\} \cap \mathrm{dom}(M_c)$ when $M_c(w)$ is $\mathbf{jd}\ w'$;
4. $\mathrm{succ}(w) \ne \emptyset$ when $M_c(w)$ is $\mathbf{jmp}\ r_s$;
5. $\mathrm{succ}(w) = \emptyset$ when $M_c(w)$ is $\mathbf{illegal}$;
6. for all $w_0, w_1$, either $\mathrm{succ}(w_0) \cap \mathrm{succ}(w_1) = \emptyset$ or $\mathrm{succ}(w_0) = \mathrm{succ}(w_1)$.

A *destination* is a successor of a computed jump. By condition 6 the destinations fall into equivalence classes, each named by an identifier (ID), and $\mathrm{dst}(w)$
is the ID of the successors of the computed jump at $w$.

## Depends on

- [Machine code under a memory-corrupting attacker](machine-code-under-attack.md)

## Sources

- M. Abadi, M. Budiu, Ú. Erlingsson and J. Ligatti, "Control-flow integrity: principles, implementations, and applications", *ACM Transactions on Information and System Security* 13(1), 2009; author version of February 2007 at <https://cseweb.ucsd.edu/~dstefan/cse127-winter19/papers/abadi:cfi.pdf>: Section 6.3, the properties (1)–(6) of a CFG, destinations and IDs.
