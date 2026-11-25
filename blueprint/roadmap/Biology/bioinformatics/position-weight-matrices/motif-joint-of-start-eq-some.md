# The joint likelihood is the window model

If $q(b) > 0$ for every $b$ and $z$ has start $j$, then the [joint likelihood](motif-joint.md) is

$$\pi(z) \prod_{k < n + w} \begin{cases} \theta_{k - j}(x_k) & j \le k < j + w,\\ q(x_k) & \text{otherwise.}\end{cases}$$
