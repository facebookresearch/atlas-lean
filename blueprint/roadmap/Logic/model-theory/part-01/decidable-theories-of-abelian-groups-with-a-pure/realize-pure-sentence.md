# Truth of a prenex sentence about pure subgroups

Let $A$ be an abelian group. A subgroup $B$ of an abelian group $A$ is pure if $nA \cap B = nB$ for every integer $n$, that is, whenever $na \in B$ with $n \in \mathbb{Z}$ and $a \in A$, there is $b \in B$ with $nb = na$. Truth of a prenex formula with matrix $\varphi$ and prefix $q$, whose first quantifier binds the variable of index $i$, under an element assignment $x : \mathbb{N} \to A$ and a subgroup assignment $X : \mathbb{N} \to \{\text{subgroups of } A\}$, is defined by recursion on $q$:

- for the empty prefix, the formula holds if every clause of $\varphi$ contains a literal whose atom holds under $(x, X)$ exactly when the literal is positive;
- $\forall x_i$ followed by $q'$ holds if for every $a \in A$ the formula with prefix $q'$ and starting index $i + 1$ holds under $(x[i \mapsto a], X)$; $\exists x_i$ is the same with "some $a \in A$";
- $\forall X_i$ followed by $q'$ holds if for every pure subgroup $B$ of $A$ the formula with prefix $q'$ and starting index $i + 1$ holds under $(x, X[i \mapsto B])$; $\exists X_i$ is the same with "some pure subgroup $B$".

Thus subgroup quantifiers range over the pure subgroups of $A$. Each quantifier, of either sort, advances the shared index by one.
