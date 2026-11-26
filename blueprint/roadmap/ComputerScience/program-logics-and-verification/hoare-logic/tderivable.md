# Total-correctness Hoare logic

Derivability of total-correctness Hoare triples
$\{P\}\,c\,\{Q\}$, for assertions $P$, $Q$ (predicates on states) and IMP commands $c$, is the
least relation closed under the following rules. In an assertion, $b$ for a boolean expression
means that $b$ evaluates to true and $\neg b$ that it evaluates to false. Skip:
$\{Q\}\,\mathtt{skip}\,\{Q\}$. Assignment: for a variable $x$ and an arithmetic expression $a$,
$\{Q[a/x]\}\,x := a\,\{Q\}$, where $Q[a/x]$ holds in a state $s$ iff $Q$ holds in $s$ updated at
$x$ to the value of $a$ in $s$. Sequencing: from $\{P\}\,c_1\,\{R\}$ and $\{R\}\,c_2\,\{Q\}$
derive $\{P\}\,c_1; c_2\,\{Q\}$. Conditional: from $\{P \wedge b\}\,c_1\,\{Q\}$ and
$\{P \wedge \neg b\}\,c_2\,\{Q\}$ derive
$\{P\}\,\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2\,\{Q\}$. Loop (variant rule): for an
assertion $I$ and a map $V$ from states to natural numbers, if for every natural number $n$ the
triple $\{I \wedge b \wedge V = n\}\,c\,\{I \wedge V < n\}$ is derivable, derive
$\{I\}\,\mathtt{while}\ b\ \mathtt{do}\ c\,\{I \wedge \neg b\}$. Consequence: if $P$ entails $P'$,
$\{P'\}\,c\,\{Q'\}$ is derivable and $Q'$ entails $Q$, derive $\{P\}\,c\,\{Q\}$, where entailment
is pointwise implication.
