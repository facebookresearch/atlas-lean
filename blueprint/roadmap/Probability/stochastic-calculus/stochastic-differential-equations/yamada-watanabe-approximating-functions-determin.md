# Yamada–Watanabe approximating functions

Let $h:\mathbb R\to\mathbb R$ be continuous and strictly increasing on $[0,\infty)$ with $h(0)=0$, and suppose that for every $\varepsilon>0$

$$\int_0^\varepsilon\frac{du}{h(u)^2}=\infty$$

as an extended-real Lebesgue integral. Then there is a strictly decreasing sequence $a_0=1>a_1>a_2>\dots>0$ with $a_n\to0$ and

$$\int_{a_{n+1}}^{a_n}\frac{du}{h(u)^2}=n+1\qquad(n\ge0),$$

and there are even functions $\varphi_n\in C^2(\mathbb R)$, $n\ge0$, such that $\varphi_n(x)\to|x|$ for every $x$, $|\varphi_n'|\le1$,

$$0\le\varphi_n''(x)\le\frac{2}{(n+1)\,h(|x|)^2}\qquad(x\ne0),$$

$\varphi_n''(0)=0$, and $\varphi_n''(x)\ne0$ only when $a_{n+1}<|x|<a_n$. For $h(u)=\sqrt u$ one may take $a_n=e^{-n(n+1)/2}$, since $\int_{a_{n+1}}^{a_n}du/u=\log(a_n/a_{n+1})=n+1$.
