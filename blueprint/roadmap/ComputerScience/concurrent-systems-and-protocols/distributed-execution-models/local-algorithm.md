# Algorithm in the LOCAL model

An algorithm $A$ in the LOCAL model, with inputs in a set $I$, states in $S$, messages in $M$ and outputs in $O$, is the same at every node and consists of maps $\mathrm{init} : \mathbb{N} \times I \to S$, $\mathrm{send} : S \times \mathbb{N} \to M$, $\mathrm{update} : S \times \mathcal{M}(M) \to S$ and $\mathrm{out} : S \to O$, where $\mathcal{M}(M)$ is the set of finite multisets of elements of $M$. A node with identifier $i$ and input $x$ starts in the state $\mathrm{init}(i, x)$; in each round a node in state $s$ sends the message $\mathrm{send}(s, j)$ to its neighbour with identifier $j$, and then moves to the state $\mathrm{update}(s, m)$, where $m$ is the multiset of the messages its neighbours sent it; a node in state $s$ outputs $\mathrm{out}(s)$.

## Sources

- N. Linial, "Locality in distributed graph algorithms", *SIAM Journal on Computing* 21(1):193–201, 1992: §1.
- J. Suomela, *Distributed Algorithms*, online textbook, 2014–2019, Aalto University (PDF version of 2 January 2021), <https://jukkasuomela.fi/da/>: §4.3.1–4.3.2, adapted without degrees, ports or stopping states.
