# Trace inclusion and trace equivalence of security protocols

One protocol is trace included in another when every sequence of attacker interactions with the first, together with the messages it reveals, can be matched by the second so that the attacker cannot tell the two revealed sets of messages apart.

For protocols in the process model of [ping-pong protocols with one message variable per rule](ping-pong-protocols-with-one-variable.md), a trace of $P$ is a pair $(\mathrm{tr}, \sigma)$ of a sequence of visible input and output actions and the resulting frame. A *recipe* is a term of $T(\Sigma_{pub}, \mathcal{N}_{pub}, \mathcal{W})$, built from public function symbols, public names and the frame variables $\mathcal{W}$; for a frame $\sigma$, $R\sigma{\downarrow}$ is the normal form of $R\sigma$, and it is a *message* when it lies in $T(\Sigma, \mathcal{N})$ (a failed decryption or signature check leaves a destructor in it). Two frames $\sigma_1$ and $\sigma_2$ are *statically equivalent*, $\sigma_1 \sim \sigma_2$, if $\mathrm{dom}(\sigma_1) = \mathrm{dom}(\sigma_2)$ and

- for every recipe $R$, $R\sigma_1{\downarrow}$ is a message if and only if $R\sigma_2{\downarrow}$ is a message, so the success of a computation is visible; and
- for all recipes $R_1, R_2$ such that $R_1\sigma_1{\downarrow}$ and $R_2\sigma_1{\downarrow}$ are messages, $R_1\sigma_1{\downarrow} = R_2\sigma_1{\downarrow}$ if and only if $R_1\sigma_2{\downarrow} = R_2\sigma_2{\downarrow}$

(Definition 2.4 of the source). $P \sqsubseteq Q$ if for every trace $(\mathrm{tr}, \sigma)$ of $P$ there is a trace $(\mathrm{tr}', \sigma')$ of $Q$ with $\mathrm{tr} = \mathrm{tr}'$ and $\sigma \sim \sigma'$; $P$ and $Q$ are trace equivalent if $P \sqsubseteq Q$ and $Q \sqsubseteq P$ (Definition 2.6 of the source).

## Depends on

- [Ping-pong protocols with one message variable per rule](ping-pong-protocols-with-one-variable.md)

## Proof depends on

None.

## Expansion

Static equivalence is the notion of indistinguishability of attacker knowledge used throughout symbolic protocol analysis. For protocols of $C_{pp}$, trace inclusion can be checked on traces made of input-output blocks only (Proposition 3.4 of the source).

## Sources

- Rémy Chrétien, Véronique Cortier and Stéphanie Delaune, "From security protocols to pushdown automata", *ACM Transactions on Computational Logic* 17(1), Article 3, 45 pages, 2015, doi:10.1145/2811262; read in the authors' open-access copy at <https://members.loria.fr/VCortier/files/Papers/CCD-Tocl15.pdf>: Section 2.1 (terms and recipes), Section 2.3 (Definitions 2.4 and 2.6: static equivalence, trace inclusion and trace equivalence) and Definition 3.3 and Proposition 3.4 of that copy.
