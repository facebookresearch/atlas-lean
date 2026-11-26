# The BAN logic of authentication

The logic of Burrows, Abadi and Needham is a many-sorted modal logic over principals $P, Q, R$, keys $K$ and formulas $X, Y$, with conjunction (written with a comma)
and the constructs: $P \mathrel{|\!\equiv} X$ ($P$ believes $X$), $P \triangleleft X$ ($P$ sees $X$), $P \mathrel{|\!\sim} X$ ($P$ once said $X$), $P \Rightarrow X$ ($P$ has jurisdiction over
$X$), $\#(X)$ ($X$ is fresh), $P \overset{K}{\leftrightarrow} Q$ ($K$ is a good shared key for $P$ and $Q$), $\overset{K}{\mapsto} P$ ($K$ is $P$'s public key),
$P \overset{X}{\rightleftharpoons} Q$ ($X$ is a secret shared by $P$ and $Q$), $\{X\}_K$ ($X$ encrypted under $K$, an abbreviation of $\{X\}_K$ *from* $R$ that records the originator $R$, so that principals recognize their own messages) and $\langle X\rangle_Y$ ($X$ combined with the secret $Y$). Its
postulates include

- *message meaning* for shared keys: from $P \mathrel{|\!\equiv} Q \overset{K}{\leftrightarrow} P$ and $P \triangleleft \{X\}_K$ infer $P \mathrel{|\!\equiv} Q \mathrel{|\!\sim} X$, where the seen message is $\{X\}_K$ from $R$ with $R \ne P$ (so $P$ did not send it itself); similarly for public keys (from $P \mathrel{|\!\equiv} \overset{K}{\mapsto} Q$ and $P \triangleleft \{X\}_{K^{-1}}$) and for shared secrets (from $P \mathrel{|\!\equiv} Q \overset{Y}{\rightleftharpoons} P$ and $P \triangleleft \langle X\rangle_Y$);
- *nonce verification*: from $P \mathrel{|\!\equiv} \#(X)$ and $P \mathrel{|\!\equiv} Q \mathrel{|\!\sim} X$ infer $P \mathrel{|\!\equiv} Q \mathrel{|\!\equiv} X$, for $X$ containing no encryption;
- *jurisdiction*: from $P \mathrel{|\!\equiv} Q \Rightarrow X$ and $P \mathrel{|\!\equiv} Q \mathrel{|\!\equiv} X$ infer $P \mathrel{|\!\equiv} X$;
- a principal who sees a formula sees its components, decrypting with keys it knows (for encrypted messages from some $R \ne P$), and a formula is fresh if one of its parts is.

A protocol is analysed by idealizing each message as a formula, stating the initial beliefs, and deriving the final beliefs of the principals.

## Sources

- M. Burrows, M. Abadi and R. Needham, "A logic of authentication", *ACM Transactions on Computer Systems* 8(1):18–36, 1990: Section 2.1 (basic notation, including "$\{X\}_K$ from $P$"), Section 2.2 (logical postulates, with the condition $R \ne P$ on the message-meaning rule for shared keys), Section 2.4 (idealized protocols) and Section 2.5 (protocol analysis).
