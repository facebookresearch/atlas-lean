# Moser-Tardos resampling algorithm in the variable model

Let $(\sigma_v)_{v \in \mathcal{V}}$ be finitely many mutually independent random variables, $\sigma_v \sim \mu_v$, and let $A_1, \dots, A_m$ be events, each $A_i$ determined by the variables in a set $\mathrm{vbl}(A_i) \subseteq \mathcal{V}$. Two events are *adjacent* if they are distinct and share a variable. The *Moser-Tardos algorithm* samples every variable afresh, and while some event holds, a *selection rule* picks one event that holds and resamples all its variables independently. The randomness is a *resampling table* of independent samples $T(v, k) \sim \mu_v$, the value of $v$ after its $k$-th resampling; a run is recorded by its *log* (the sequence of resampled events), and a selection rule is *valid* if it only picks events that hold in the current assignment. The rule may be deterministic or randomized and may even inspect the whole table.

## Depends on

- [Lovász local lemma, general form](../../../Combinatorics/probabilistic-combinatorics/lovasz-local-lemma-general-finite.md)

## Sources

- Robin A. Moser and Gábor Tardos, "A Constructive Proof of the General Lovász Local Lemma", Journal of the ACM 57(2), 2010.
