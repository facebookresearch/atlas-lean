# Worst-case bounds for a mean with missing outcomes

Let $Y$ lie almost surely in a known interval $[a,b]$, and let $R\in\{0,1\}$ indicate whether $Y$ is observed. Write $q=P(R=1)$ and $A=E[RY]$, where $RY=0$ for nonrespondents. Among all laws with the same observed law of $(R,RY)$ and with outcomes in $[a,b]$ almost surely, the set of compatible values of $E[Y]$ is exactly $[A+(1-q)a,\ A+(1-q)b]$.

Indeed, the observed law fixes both $A$ and $q$. The contribution of nonrespondents to the mean is between $(1-q)a$ and $(1-q)b$. Filling every missing outcome with a constant $t\in[a,b]$ preserves the observed law and gives mean $A+(1-q)t$, which attains every point of the interval.

For $q>0$, $A=q\mu_1$ with $\mu_1=E[Y\mid R=1]$. For $q=1$, the interval is the single point $\mu_1$. For $q=0$, $A=0$ and the interval is $[a,b]$.

## Sources

- Lecture slides, *5b. Partial Identification* (course ISS5096), Slide 2, “No-Assumption Bounds”, <https://j1yoo.github.io/assets/courses/eci/ECI_05b_Partial_Identification.pdf>. The slides use the same bounding argument for unobserved potential outcomes in the average treatment effect. The sharp interval for a single mean is derived here.
