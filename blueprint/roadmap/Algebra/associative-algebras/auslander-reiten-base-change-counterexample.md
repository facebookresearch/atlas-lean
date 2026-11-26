# A base-change-stable Auslander–Reiten counterexample

The three coordinate parameters are algebraically independent over $\mathbb F_2$ in $K=\mathbb F_2(t_0,t_1,t_2)$. There are a finite-dimensional $K$-algebra $R$ and a finite-dimensional nonprojective left module $Z$ such that $\operatorname{Ext}^i_R(Z,Z)=\operatorname{Ext}^i_R(Z,R)=0$ for all $i>0$, $R/\operatorname{rad} R\cong K^8$ as a $K$-algebra, and $(\operatorname{rad}R)^4\ne0$.

The module $Z$ has a two-sided exact chain complex $(P_i,d_i)$ of finite projectives with $Z\cong P_0/\operatorname{im}d_1$. For every projective left $R$-module $Q$, any $f:P_i\to Q$ with $fd_{i+1}=0$ factors through $d_i:P_i\to P_{i-1}$. For every field extension $E/K$, the base-changed algebra and module admit the tensor action $(a\otimes r)(b\otimes z)=ab\otimes rz$ compatible with $E$-scalars, and satisfy **all** these dimension, nonprojectivity, complex, Ext and radical conclusions over $E$.

## Depends on

- Algebraic independence in the rational function field, radical and Ext, and tensor base-change for left modules.

## Proof depends on

- Construction of the finite algebra and totally acyclic witness, persistence of radical and Ext properties after any field base change.

## Expansion

Break out the algebra presentation and radical layers, verify the complex exactness and Hom exactness, then prove that neither nonprojectivity nor any required conclusion is lost under extension.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/AuslanderReiten.lean#L70-L72) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/AuslanderReiten.lean).
