# Binary structural causal model with shared noise

A binary structural causal model on two observed nodes $X \to Y$ with exogenous noise in a type $U$ consists of

- noise weights $p_U : U \to \mathbb{R}$;
- a structural equation $X = f_X(u)$ with $f_X : U \to \{0,1\}$;
- a structural equation $Y = f_Y(X, u)$ with $f_Y : \{0,1\} \times U \to \{0,1\}$.

Counterfactual quantities evaluate every intervened world at the same noise value $u$. The weights are not required to form a probability mass function; that is a separate condition.
