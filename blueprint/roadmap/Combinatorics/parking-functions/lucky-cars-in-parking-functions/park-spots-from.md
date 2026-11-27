# Greedy parking from an occupied set

Number the $n$ spots $0, \dots, n-1$. Given a list
$a_1, \dots, a_m$ of preferred spots and a set $S$ of occupied spots, cars $1, \dots, m$ arrive in
order and car $k$ takes the least spot at or after $a_k$ that is neither in $S$ nor taken by cars
$1, \dots, k-1$ (or $a_k$ itself if there is none). The result is the list of spots taken, in
arrival order.
