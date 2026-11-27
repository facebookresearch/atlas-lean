# Balanced type configurations of deconfined global types

Deconfined global types split each asynchronous communication into a separate output and input. A type configuration pairs such a global type with a queue of pending messages; it is balanced when every input can be matched by a queued or earlier output and every queued message is eventually read.

**Global types.** Fix sets of participants and labels. Global types are the regular (finitely many distinct subterms), possibly infinite terms generated coinductively by

$$
\mathsf{G} ::= \mathsf{End} \mid \mathsf{p}\,\mathsf{q}!\{\lambda_i; \mathsf{G}_i\}_{i \in I} \mid \mathsf{p}\,\mathsf{q}?\{\lambda_i; \mathsf{G}_i\}_{i \in I}
$$

with $I \ne \emptyset$ finite, $\mathsf{p} \ne \mathsf{q}$ and pairwise distinct labels $\lambda_i$. The output choice $\mathsf{p}\,\mathsf{q}!\{\lambda_i;\mathsf{G}_i\}$ says that $\mathsf{p}$ sends some $\lambda_k$ to $\mathsf{q}$ and the protocol continues as $\mathsf{G}_k$; the input choice $\mathsf{p}\,\mathsf{q}?\{\lambda_i;\mathsf{G}_i\}$ says that $\mathsf{q}$ receives some $\lambda_k$ from $\mathsf{p}$.

**Queues.** A message queue is a finite sequence $\mathcal{M}$ of messages $\langle \mathsf{p}, \lambda, \mathsf{q} \rangle$, taken modulo the equivalence $\equiv$ that swaps adjacent messages unless they have the same sender and the same receiver. A *type configuration* is a pair $\mathsf{G} \parallel \mathcal{M}$.

**Readability.** The judgment $\mathsf{G} \vdash_{\mathsf{read}} \mathcal{M}$ (each path of $\mathsf{G}$ reads all messages of $\mathcal{M}$) is defined inductively: it is derivable if $\mathcal{M}$ is empty; for an output choice if it is derivable for every $\mathsf{G}_i$ with the same queue; for an input choice $\mathsf{p}\,\mathsf{q}?\{\lambda_i;\mathsf{G}_i\}$ with $\mathcal{M} \equiv \langle \mathsf{p}, \lambda_h, \mathsf{q} \rangle \cdot \mathcal{M}'$ for some $h \in I$ if $\mathsf{G}_i \vdash_{\mathsf{read}} \mathcal{M}'$ for all $i \in I$; and for an input choice whose labels match no message on top of the queue (modulo $\equiv$) if $\mathsf{G}_i \vdash_{\mathsf{read}} \mathcal{M}$ for all $i \in I$.

**Balancing.** The judgment $\vdash \mathsf{G} \parallel \mathcal{M}$ is the largest relation (coinductive interpretation) closed under:

- $\vdash \mathsf{End} \parallel \emptyset$;
- $\vdash \mathsf{p}\,\mathsf{q}!\{\lambda_i;\mathsf{G}_i\}_{i\in I} \parallel \mathcal{M}$ if $\vdash \mathsf{G}_i \parallel \mathcal{M} \cdot \langle \mathsf{p}, \lambda_i, \mathsf{q} \rangle$ and $\mathsf{G}_i \vdash_{\mathsf{read}} \mathcal{M}$ for all $i \in I$;
- $\vdash \mathsf{p}\,\mathsf{q}?\{\lambda_i;\mathsf{G}_i\}_{i\in I} \parallel \langle \mathsf{p}, \lambda_h, \mathsf{q} \rangle \cdot \mathcal{M}$ for some $h \in I$ if $\vdash \mathsf{G}_h \parallel \mathcal{M}$ and $\mathsf{G}_i \vdash_{\mathsf{read}} \mathcal{M}$ for all $i \in I$.

*Weak balancing* is the same coinductive definition without the readability side conditions. A configuration is called (weakly) balanced if the corresponding judgment is derivable; balancing is the well-formedness condition the paper uses to prove progress of well-typed sessions.

## Depends on

None.

## Proof depends on

None.

## Expansion

Readability is decidable because global types are regular and the queue only shrinks along a readability derivation. Balancing is not: an infinite derivation may let the queue grow without bound, as in a protocol that keeps sending before it reads. The paper therefore also gives a sound inductive algorithm that accepts a subclass of balanced configurations.

## Sources

- Francesco Dagnino, Paola Giannini and Mariangiola Dezani-Ciancaglini, "Deconfined Global Types for Asynchronous Sessions", Logical Methods in Computer Science 19(1), Article 3, 2023, <https://doi.org/10.46298/lmcs-19(1:3)2023>; Section 2 (message queues and $\equiv$), Section 3 (global types, weak balancing and the figure "Balancing of type configurations") of arXiv:2111.11984v6, <https://arxiv.org/abs/2111.11984v6>.
