# Zone thermal network as a state-space plant

Let `ι` be a finite index set of zones with decidable equality, with capacities `C i`, inter-zone
conductances `G i j` and boundary conductances `g0 i`. The thermal plant is the linear state-space
system with the [state matrix](thermal-a.md), the [input matrix](thermal-b.md), the
[output matrix](thermal-c.md) and the [feedthrough matrix](thermal-d.md): state the zone
temperatures, input the outside temperature and the heating powers, output the zone temperatures.
