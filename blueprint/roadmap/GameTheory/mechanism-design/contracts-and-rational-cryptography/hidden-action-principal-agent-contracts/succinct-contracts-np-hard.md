# Optimal contracts are hard to compute with succinct outcome spaces

Consider principal-agent instances whose outcome space is $\{0, 1\}^d$, where each action $i$ induces a product distribution in which coordinate $\ell$ equals $1$ independently with probability $q_{i,\ell}$, and the reward is additive across coordinates. Computing an optimal contract is NP-hard in this model, and it remains NP-hard to approximate the optimal principal utility within some constant factor; by contrast the optimal linear contract is computable in polynomial time.

## Proof sketch

Reduce from a gap version of a covering problem: coordinates encode elements, actions encode sets with suitable success probabilities, and payments must single out joint outcomes characteristic of the intended action. With product distributions, the min-pay programs have exponentially many variables, and the reduction shows that distinguishing whether a cheap separating contract exists is as hard as the covering gap problem. Linear contracts only need expected rewards, which are computable coordinatewise.

## Depends on

- [Hidden-action principal-agent instance and contract](hidden-action-principal-agent-instance.md)
- [Linear contract and its critical values](linear-contract-critical-values.md)

## Proof depends on

- [Optimal contracts via one linear program per action](optimal-contract-min-pay-linear-programs.md)

## Sources

- P. Dütting, T. Roughgarden, I. Talgam-Cohen, "The Complexity of Contracts", SODA 2020; SIAM Journal on Computing 50(1) (2021).
