# Pairwise masks reveal only the sum

Fix users $U$ with $|U|=n$ and inputs $x_u\in\mathbb{Z}_R^m$. If the masks $p_{u,v}$ for $u<v$ are independent and uniform on $\mathbb{Z}_R^m$ and $p_{v,u}=-p_{u,v}$, then the masked inputs $y_u=x_u+\sum_{v\ne u}p_{u,v}$ are distributed exactly as uniform vectors conditioned on $\sum_uy_u=\sum_ux_u$.

Formally, with all arithmetic modulo $R$,

$$
\Big\{\,p_{u,v}\leftarrow\mathbb{Z}_R^m\ (u<v),\ p_{v,u}:=-p_{u,v}\ :\ \Big(x_u+\sum_{v\in U\setminus\{u\}}p_{u,v}\Big)_{u\in U}\Big\}\equiv\Big\{\,(w_u)_{u\in U}\leftarrow\mathbb{Z}_R^m\ \text{uniform s.t.}\ \sum_{u}w_u=\sum_{u}x_u\ :\ (w_u)_{u\in U}\Big\} .
$$

In particular the masks cancel in the sum, and any party seeing all $y_u$ learns nothing about the individual inputs beyond their sum. Secure aggregation replaces the uniform masks by PRG expansions of agreed seeds, which makes the statement computational.

## Depends on

None.

## Proof depends on

None.

## Expansion

Induction on $n$, as the source indicates: for $n=1$ both sides are the point $x_u$. For $n\ge2$ fix the masks not involving the last user $u^*$; the masks $p_{u,u^*}$ for $u\ne u^*$ are independent uniform and enter only $y_u$ and (negated) $y_{u^*}$, so $(y_u)_{u\ne u^*}$ is uniform and $y_{u^*}$ is determined by the sum.

## Sources

- Keith Bonawitz, Vladimir Ivanov, Ben Kreuter, Antonio Marcedone, H. Brendan McMahan, Sarvar Patel, Daniel Ramage, Aaron Segal, Karn Seth, "Practical Secure Aggregation for Privacy-Preserving Machine Learning", ACM CCS 2017, DOI 10.1145/3133956.3133982; numbers from the full version, IACR ePrint 2017/281: Lemma 6.1.
