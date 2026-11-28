# Ping-pong protocols with one message variable per rule

Ping-pong protocols are replicated security protocols in which each rule receives one message, matches it against a pattern built from encryption and signature with at most one unknown message, and answers with a message built from that pattern and fresh randomness.

**Terms.** Messages are terms over a sorted signature with sorts for random numbers, keys (symmetric, private, public) and messages, built from names (random numbers), constants and the randomized constructors $\mathrm{senc}(m, k, r)$, $\mathrm{aenc}(m, k, r)$ and $\mathrm{sign}(m, k, r)$, with destructors $\mathrm{sdec}$, $\mathrm{adec}$ and $\mathrm{check}$ and the rewrite rules $\mathrm{sdec}(\mathrm{senc}(x, k, z), k) \to x$, $\mathrm{adec}(\mathrm{aenc}(x, k, z), k^{-1}) \to x$, $\mathrm{check}(\mathrm{sign}(x, k, z), k^{-1}) \to x$. There is no pairing and no hash function. Names are split into those drawn by the attacker and those drawn by the participants.

**Processes and traces.** Processes are built from $0$, input $\mathrm{in}(c, u).P$, output $\mathrm{out}(c, u).P$, parallel composition, replication $!P$ and name generation $\mathrm{new}\ n.P$, over public channels $c$. A configuration pairs a multiset of processes with a frame $\sigma$ recording the messages output so far. The attacker feeds inputs with messages it builds from the frame and public symbols (recipes), and outputs extend the frame. A trace of $P$ is a pair $(\mathrm{tr}, \sigma)$ of the sequence of visible input and output actions and the resulting frame.

**The class $C_{pp}$.** Fix a message variable $x$. Input terms are $u ::= x \mid s \mid f(u, k, z)$ and output terms are $v ::= x \mid s \mid f(v, k, r)$, with $s, k$ constants (or the start constant), $f \in \{\mathrm{senc}, \mathrm{aenc}, \mathrm{sign}\}$, $z$ a variable and $r$ a name, each variable or name occurring at most once. A protocol is in $C_{pp}$ if it has the form

$$
P = \big|_{i=1}^{n} \big|_{j=1}^{p_i}\ !\,\mathrm{in}(c_i, u_i^j).\mathrm{new}\ r_1 \dots \mathrm{new}\ r_{k_i^j}.\mathrm{out}(c_i, v_i^j)
$$

where the names of each output term are among the freshly generated ones, and two branches on the same channel have input terms that are not unifiable after renaming (determinism).


## Depends on

None.

## Proof depends on

None.

## Expansion

The restrictions keep the secrecy problem decidable for this class with unboundedly many sessions, and the determinism condition makes trace equivalence of two $C_{pp}$ protocols decidable, by reduction to language equivalence of real-time generalized deterministic pushdown automata.

## Sources

- Rémy Chrétien, Véronique Cortier and Stéphanie Delaune, "From security protocols to pushdown automata", *ACM Transactions on Computational Logic* 17(1), Article 3, 45 pages, 2015, doi:10.1145/2811262; read in the authors' open-access copy at <https://members.loria.fr/VCortier/files/Papers/CCD-Tocl15.pdf>: Section 2 (terms, processes, semantics and trace equivalence), Definition 3.1 (the class $C_{pp}$) and Theorem 3.5 of that copy.
