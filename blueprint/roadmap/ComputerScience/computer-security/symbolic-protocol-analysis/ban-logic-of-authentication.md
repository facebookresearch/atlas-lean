# The BAN logic of authentication

The logic of Burrows, Abadi and Needham is a many-sorted modal logic over principals $P, Q, R$, keys $K$ and formulas $X, Y$, with conjunction (written with a comma)
and the constructs: $P \mathrel{|\!\equiv} X$ ($P$ believes $X$), $P \triangleleft X$ ($P$ sees $X$), $P \mathrel{|\!\sim} X$ ($P$ once said $X$), $P \Rightarrow X$ ($P$ has jurisdiction over
$X$), $\#(X)$ ($X$ is fresh), $P \overset{K}{\leftrightarrow} Q$ ($K$ is a good shared key for $P$ and $Q$), $\overset{K}{\mapsto} P$ ($K$ is $P$'s public key),
$P \overset{X}{\rightleftharpoons} Q$ ($X$ is a secret shared by $P$ and $Q$), $\{X\}_K$ ($X$ encrypted under $K$) and $\langle X\rangle_Y$ ($X$ combined with the secret $Y$). Its
postulates include

- *message meaning* for shared keys: from $P \mathrel{|\!\equiv} Q \overset{K}{\leftrightarrow} P$ and $P \triangleleft \{X\}_K$ infer $P \mathrel{|\!\equiv} Q \mathrel{|\!\sim} X$, and similarly for public keys and shared secrets;
- *nonce verification*: from $P \mathrel{|\!\equiv} \#(X)$ and $P \mathrel{|\!\equiv} Q \mathrel{|\!\sim} X$ infer $P \mathrel{|\!\equiv} Q \mathrel{|\!\equiv} X$, for $X$ containing no encryption;
- *jurisdiction*: from $P \mathrel{|\!\equiv} Q \Rightarrow X$ and $P \mathrel{|\!\equiv} Q \mathrel{|\!\equiv} X$ infer $P \mathrel{|\!\equiv} X$;
- rules distributing belief and seeing over conjunction, decomposition of seen messages with known keys, and freshness of a formula from that of a component.

A protocol is analysed by idealizing each message as a formula, stating the initial beliefs, and deriving the final beliefs of the principals.

## Sources

- M. Burrows, M. Abadi and R. Needham, *A Logic of Authentication*, SRC Research Report 39, Digital Equipment Corporation Systems Research Center, 28 February 1989, revised 22 February 1990: Section 2, "The Formalism" (basic notation and logical postulates) and the subsections on idealized protocols and protocol analysis.
