# Trace inclusion and trace equivalence of security protocols

One protocol is trace included in another when every sequence of attacker interactions with the first, together with the messages it reveals, can be matched by the second so that the attacker cannot tell the two revealed sets of messages apart.

For protocols in the process model of [ping-pong protocols with one message variable per rule](ping-pong-protocols-with-one-variable.md), a trace of $P$ is a pair $(\mathrm{tr}, \sigma)$ of a sequence of visible input and output actions and the resulting frame. $P \sqsubseteq Q$ if for every trace $(\mathrm{tr}, \sigma)$ of $P$ there is a trace $(\mathrm{tr}', \sigma')$ of $Q$ with $\mathrm{tr} = \mathrm{tr}'$ and $\sigma$ statically equivalent to $\sigma'$ (no pair of recipes distinguishes the two frames by an equality test); $P$ and $Q$ are trace equivalent if $P \sqsubseteq Q$ and $Q \sqsubseteq P$.

## Depends on

- [Ping-pong protocols with one message variable per rule](ping-pong-protocols-with-one-variable.md)

## Proof depends on

None.

## Expansion

Static equivalence is the notion of indistinguishability of attacker knowledge used throughout symbolic protocol analysis. For protocols of $C_{pp}$, trace inclusion can be checked on traces made of input-output blocks only (Proposition 3.4 of the source).

## Sources

- Rémy Chrétien, Véronique Cortier and Stéphanie Delaune, "From security protocols to pushdown automata", *ACM Transactions on Computational Logic* 17(1), Article 3, 45 pages, 2015, doi:10.1145/2811262; read in the authors' open-access copy at <https://members.loria.fr/VCortier/files/Papers/CCD-Tocl15.pdf>: Section 2 (traces, static equivalence and trace equivalence) and Definition 3.3 and Proposition 3.4 of that copy.
