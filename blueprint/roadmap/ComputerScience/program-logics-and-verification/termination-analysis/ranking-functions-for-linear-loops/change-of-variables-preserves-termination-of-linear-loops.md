# Change of variables preserves termination of linear loops

Let $A$ be a real $N \times N$ matrix, $B$ a real $m \times N$ matrix and $P$ an invertible real $N \times N$ matrix. The homogeneous linear loop

$$P_2 : \mathbf{while}\ (Bx > 0)\ \{\, x := Ax \,\}$$

terminates on every input $x \in \mathbb{R}^N$ if and only if the loop

$$P_3 : \mathbf{while}\ (BPy > 0)\ \{\, y := P^{-1} A P y \,\}$$

terminates on every input: a nonterminating input $c$ of $P_2$ gives the nonterminating input $P^{-1} c$ of $P_3$, and a nonterminating input $d$ of $P_3$ gives the input $P d$ of $P_2$. Choosing $P$ to bring $A$ to its real Jordan form reduces termination to loops with block-diagonal update.

## Sources

- A. Tiwari, "Termination of linear programs", *Computer Aided Verification (CAV 2004)*, LNCS 3114, Springer, 2004, pp. 70–82, author copy <https://www.csl.sri.com/users/tiwari/papers/cav04.pdf>, Section 3, Proposition 1 and the paragraph after its proof.
