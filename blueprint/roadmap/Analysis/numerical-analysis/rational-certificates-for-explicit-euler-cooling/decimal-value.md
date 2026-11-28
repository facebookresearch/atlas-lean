# Positional value of a run of decimal digits

For a list of characters $d_1 d_2 \dots d_m$ (most significant first), the positional value is

$$\sum_{i=1}^{m} v(d_i)\, 10^{\,m-i},$$

where $v$ is the digit value. Leading zeros do not change the value, and the empty list has value $0$.
