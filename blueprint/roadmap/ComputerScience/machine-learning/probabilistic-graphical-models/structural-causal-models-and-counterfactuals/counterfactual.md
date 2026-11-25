# The unit-level counterfactual

**The unit-level counterfactual** (Pearl, *Statistics Surveys* 2009, Definition 4,
eq. (27)): let $M$ be a Markovian structural causal model on the nodes $0, \dots, n - 1$ with
values in $\alpha$, $W$ a finite set of nodes and $w \in \alpha^n$. For a disturbance value $u$,
$X_{W \leftarrow w}(u)$, the values the endogenous variables would have taken in the unit with
disturbances $u$ had $X_W$ been $w$, is the solution of the [submodel](do-set.md)
$\mathrm{do}(X_W = w)$ at $u$.

## Related topics

- [The single-node counterfactual in a structural causal model with node-wise noise](counterfactual-2.md): the counterfactual for an intervention on a single node, in the model with node-wise noise sets.
