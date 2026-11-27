# BCMP networks

The product form of [Jackson networks](jackson-networks.md) and [Gordon–Newell networks](gordon-newell-networks.md) persists in a larger class of networks, known by the initials of Baskett, Chandy, Muntz and Palacios. The stationary distribution of the numbers of customers keeps the same product form when:

1. instead of first-come first-served service with exponential service times, some stations use processor sharing, in which the $j$ customers present are all served simultaneously at speed $1/j$ each, or last-come first-served preemptive resume, with general service-time distributions of mean $1/\mu_i$; the product form depends on these distributions only through their means;
2. a first-come first-served station may have a service intensity $\mu_i(n_i)$ depending on its number $n_i$ of customers, in particular $c_i$ servers ($\mu_i(n_i) = \min(n_i, c_i)\mu_i$) or infinitely many, and the insensitivity to the service-time distribution again holds for infinite-server stations;
3. there are several customer classes, each with its own arrival rates, service rates and routing probabilities, some open and some closed, provided that at a first-come first-served station all classes have exponential service times with the same rate; the joint distribution of the numbers of customers of each class at each station then has a double product form, over stations and over classes.

## Depends on

- [Product-form stationary distribution of a Jackson network](jackson-networks.md)
- [Product-form stationary distribution of a Gordon–Newell network](gordon-newell-networks.md)

## Expansion

This family node becomes ready once it is split into precise statements, each with the state descriptor it needs:

- the processor-sharing and last-come first-served preemptive-resume stations with general (for instance Coxian) service times, and the state that records the service phases;
- load-dependent and infinite-server stations;
- multiclass routing with open and closed chains and the traffic equations per chain;
- a check of each statement against F. Baskett, K. M. Chandy, R. R. Muntz and F. G. Palacios, "Open, closed, and mixed networks of queues with different classes of customers", *Journal of the ACM* 22(2):248–260, 1975.

## Sources

- O. J. Boxma, *Stochastic Performance Modelling*, lecture notes, Eindhoven University of Technology, January 5, 2017, <https://www.win.tue.nl/~iadan/2WB60/lecturenotes.pdf>, Section 7.7 (generalizations 1 and 2 and the multiclass extension, stated there without proof).
