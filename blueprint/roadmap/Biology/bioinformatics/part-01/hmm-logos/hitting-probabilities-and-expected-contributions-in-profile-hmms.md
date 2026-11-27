# Hitting probabilities and expected contributions in profile HMMs

**Setting.** A profile HMM of length $L$ (Plan7 topology, as in HMMER) has match states $M_i$ and silent delete states $D_i$ for $i = 1,\dots,L$, insert states $I_i$ for $i = 1,\dots,L-1$, a begin state $B$ and an end state $E$, with transition probabilities $A_{s,t}$. From each position the allowed transitions are $M_i \to I_i, M_{i+1}, D_{i+1}$; $D_i \to M_{i+1}, D_{i+1}$; and $I_i \to M_{i+1}$ together with the self-loop $I_i \to I_i$. The **hitting probability** $h(s)$ of a state is the probability that a random path $B \to \cdots \to E$ visits $s$. The **contribution** $C(s)$ of an emitting state is the number of letters it emits along the path, with expectation $c(s) = E[C(s)]$.

**Proposition (hitting probabilities).** Every path passes through exactly one of $M_i, D_i$, so $h(D_i) = 1 - h(M_i)$. For the Plan7 topology,

$$h(I_i) = h(M_i)\,A_{M_i, I_i}, \qquad h(M_{i+1}) = h(M_i)\,A_{M_i,M_{i+1}} + h(D_i)\,A_{D_i,M_{i+1}} + h(I_i),$$

starting from $h(M_1) = A_{B,M_1}$; all hitting probabilities follow by one forward pass in $O(L)$ time despite the infinitely many paths created by insert self-loops. Topologies that also allow $D_i \to I_i$ and $I_i \to D_{i+1}$ (as in SAM) are handled the same way, with an extra factor for the probability that a path leaving $I_{i-1}$ exits into $M_i$ rather than $D_i$.

**Proposition (expected contributions).** $c(M_i) = h(M_i)$, and since a visit to $I_i$ emits a geometric number of letters with exit probability $1 - A_{I_i,I_i}$,

$$c(I_i) = \frac{h(I_i)}{1 - A_{I_i, I_i}} \ge h(I_i).$$

By linearity of expectation, the expected length of an emitted sequence is $\sum_{i=1}^{L} h(M_i) + \sum_{i=1}^{L-1} \dfrac{h(I_i)}{1 - A_{I_i,I_i}}$.

**HMM logo.** Each emitting state receives a letter stack whose width is $c(s)$, so total logo width equals the expected sequence length, with insert stacks shaded to separate $h(s)$ from $c(s) - h(s)$; stack height is the information content of the state's emission distribution relative to the background, and letter heights are proportional to emission probabilities.

## Depends on

- [Profile hidden Markov model](../../sequence-alignment/profile-hidden-markov-models/profile-hmm.md)
- [Information content of a position weight matrix column](../../position-weight-matrices/info-content.md)

## Expansion

There are three ways into $M_{i+1}$ (from $M_i$, from $D_i$, and from $I_i$, which can only exit forward into $M_{i+1}$ in Plan7), and one way into $I_i$, which gives the recursion; self-loops change how long a path stays in $I_i$ but not whether it reaches $M_{i+1}$. Widths make positions that are often deleted visibly narrow and long insertions visibly wide, information that an ordinary sequence logo of the match emissions discards. Comparing logos of homologous subfamilies (Rab versus Ras GTPases) highlights positions where conservation or insertion behaviour differs.

## Sources

- B. Schuster-Böckler, J. Schultz, S. Rahmann, "HMM Logos for visualization of protein families", BMC Bioinformatics 5:7 (2004), Definitions 1–2 and Propositions 1–3, <https://doi.org/10.1186/1471-2105-5-7>, PMCID PMC341448.
