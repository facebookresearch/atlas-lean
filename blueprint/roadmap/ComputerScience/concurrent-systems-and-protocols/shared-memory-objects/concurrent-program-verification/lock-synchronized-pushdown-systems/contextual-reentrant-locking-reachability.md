# Pairwise reachability under contextual reentrant locking is undecidable

For two threads that communicate only through reentrant locks and follow contextual locking, it is undecidable whether given control states of the two threads can be reached simultaneously, even when both threads are finite-state. With contextual non-reentrant locks the same problem is decidable in polynomial time.

**Setting (Bonnet, Chadha, Viswanathan and Madhusudan).** Fix a finite set $\mathcal{L}$ of locks. A pushdown system using $\mathcal{L}$ is a tuple $(Q, \Gamma, q_s, \delta)$ with finite control states $Q$, finite stack alphabet $\Gamma$, initial state $q_s$, and transitions of five kinds: internal moves $Q \times Q$, pushes $Q \times (Q \times \Gamma)$ (procedure calls), pops $(Q \times \Gamma) \times Q$ (returns), acquisitions $Q \times (Q \times \mathcal{L})$ and releases $(Q \times \mathcal{L}) \times Q$. With *reentrant* locks a thread's configuration is $(q, w, h)$ with $h : \mathcal{L} \to \mathbb{N}$ counting how often it holds each lock: it may acquire $l$ when $l$ is free (held by no thread) or when $h(l) > 0$, and each release decrements $h(l)$, freeing $l$ when the count returns to $0$. A 2-PDS $(\mathcal{P}_1, \mathcal{P}_2)$ interleaves the two threads from the initial configuration in which both are in their initial states with empty stacks and hold no locks. Thread $i$ *follows contextual locking* if, along every computation, for each matching procedure call (at step $\ell$) and return (at step $j$) it holds exactly the same lock counts just before the call and just after the return, and at no step in between holds fewer instances of any lock than before the call. The *pairwise reachability problem* asks, given control states $q_1$ of $\mathcal{P}_1$ and $q_2$ of $\mathcal{P}_2$, whether some computation reaches a configuration in which $\mathcal{P}_1$ is in $q_1$ and $\mathcal{P}_2$ is in $q_2$.

**Theorem.** The following problem is undecidable: given a 2-PDS $(\mathcal{P}_1, \mathcal{P}_2)$ communicating only through reentrant locks, in which both threads follow contextual locking, and control states $q_1, q_2$, decide pairwise reachability of $(q_1, q_2)$. It remains undecidable when $\mathcal{P}_1$ and $\mathcal{P}_2$ never use their stacks (finite-state threads).

The set of locks is part of the input, although the reduction uses only eight locks. For contextual non-reentrant locking the paper gives a polynomial-time algorithm, and pairwise reachability for threads synchronizing through unrestricted locks with recursion is known to be undecidable.

## Depends on

- [Pushdown automaton](../../../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/pushdown-automata/pda.md)
- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from the halting problem of two-counter machines started with both counters at zero. Thread $\mathcal{P}_1$ tracks the control state and stores counter $i$ as the number of instances of a reentrant lock $l_i$ it holds: increments acquire $l_i$, decrements release it. A zero test of counter $i$ needs the cooperation of $\mathcal{P}_2$, which must be able to acquire $l_i$, possible only when $\mathcal{P}_1$ holds no instance of it; a handshake through locks $r_i, t_i$ forces the two threads to interleave the sequences $\mathrm{acq}(t_i)\,\mathrm{rel}(r_i)\,\mathrm{acq}(l_i)\,\mathrm{rel}(t_i)\,\mathrm{acq}(r_i)\,\mathrm{rel}(l_i)$ and $\mathrm{acq}(l_i)\,\mathrm{rel}(t_i)\,\mathrm{acq}(r_i)\,\mathrm{rel}(l_i)\,\mathrm{acq}(t_i)\,\mathrm{rel}(r_i)$ in lockstep. Two more locks set up the initially held locks. No procedure calls occur, so contextual locking holds trivially, and the target pair is reachable exactly when the machine halts.

## Sources

- Rémi Bonnet, Rohit Chadha, Mahesh Viswanathan and P. Madhusudan, "Reachability under Contextual Locking", Logical Methods in Computer Science 9(3), Article 21, 2013, <https://doi.org/10.2168/LMCS-9(3:21)2013>; read in arXiv:1308.2349v3, <https://arxiv.org/abs/1308.2349v3>: Lemma 4.1 in Section 4 ("Reentrant locking"), the definitions of Sections 2 ("Model") and 3 ("Pairwise reachability"), and the abstract (polynomial-time decidability without reentrance), in the numbering of that version.
