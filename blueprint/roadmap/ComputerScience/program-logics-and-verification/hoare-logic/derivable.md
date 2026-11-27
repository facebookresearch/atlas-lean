# Derivability in Hoare logic for partial correctness

Here an assertion is a predicate on
states, and an assertion $P$ entails an assertion $P'$ when every state satisfying $P$ satisfies
$P'$. For an assertion $P$ and a Boolean expression $b$, the assertion $P \land b$ holds in a
state when $P$ holds there and $b$ evaluates to true in it, and the assertion $P \land \lnot b$
holds in a state when $P$ holds there and $b$ evaluates to false in it. Derivability of
partial-correctness Hoare triples $\{P\}\,c\,\{Q\}$ is the least relation closed under the
following rules, where $P$, $P'$, $Q$, $Q'$, $R$ and $I$ are assertions, $c$, $c_1$ and $c_2$ are
commands, $x$ is a variable, $a$ is an arithmetic expression and $b$ is a Boolean expression.

* Skip: $\{Q\}\,\mathtt{skip}\,\{Q\}$.
* Assignment: $\{Q[a/x]\}\,x := a\,\{Q\}$, where $Q[a/x]$ holds in a state $s$ when $Q$ holds in
  the state obtained from $s$ by setting $x$ to the value of $a$ in $s$.
* Sequencing: from $\{P\}\,c_1\,\{R\}$ and $\{R\}\,c_2\,\{Q\}$ derive $\{P\}\,c_1; c_2\,\{Q\}$.
* Conditional: from $\{P \land b\}\,c_1\,\{Q\}$ and $\{P \land \lnot b\}\,c_2\,\{Q\}$ derive
  $\{P\}\,\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2\,\{Q\}$.
* While: from $\{I \land b\}\,c\,\{I\}$ derive
  $\{I\}\,\mathtt{while}\ b\ \mathtt{do}\ c\,\{I \land \lnot b\}$.
* Consequence: if $P$ entails $P'$, $\{P'\}\,c\,\{Q'\}$ is derivable and $Q'$ entails $Q$, then
  $\{P\}\,c\,\{Q\}$ is derivable.
